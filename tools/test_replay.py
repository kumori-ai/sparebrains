"""The worst-lane replay (2026-10-24): a frozen cohort of one lane's raw replies re-run with zero model calls through
extraction with and without Lean 3 recovery, the chain, and tools alone. No Lean here: stand-in judges."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ledger_files
import proof_text
import replay
import subgoals

NAME = "t"
HEAD = f"theorem {NAME} (a b : ℕ) : a + b = b + a :="


def half_problem(half, tset="s"):
    """A target name in set `tset` on the given half."""
    i = 0
    while replay.problem_half(tset, f"p{i}") != half:
        i += 1
    return f"p{i}"


class Lean3Recovery(unittest.TestCase):
    def test_a_closed_begin_end_body_is_recovered_and_marked(self):
        reply = HEAD + "\nbegin\n  rw add_comm,\nend\n\nThis proves it."
        body, how = proof_text.recover_lean3(reply, NAME)
        self.assertEqual([l.strip() for l in body.strip().splitlines()], ["begin", "rw add_comm,", "end"])
        self.assertEqual(how, ["lean3_begin"])

    def test_a_truncated_body_drops_its_broken_last_line_and_closes_open_braces(self):
        reply = HEAD + "\nbegin\n  have h : a = a,\n  { refl },\n  have k : b = b,\n  { rw [div_mul, div_mul, div_"
        body, how = proof_text.recover_lean3(reply, NAME)
        lines = [l.strip() for l in body.splitlines()]
        self.assertNotIn("rw [div_mul, div_mul, div_", " ".join(lines))
        self.assertEqual(lines[-2:], ["have k : b = b,", "end"], "the broken line goes with its own brace")
        self.assertEqual(how, ["lean3_begin", "truncated_closed"])

    def test_a_final_end_after_unclosed_inner_braces_still_closes_them(self):
        # attempt 15335's shape: inner `{` blocks never closed, then `end` and prose
        reply = HEAD + "\nbegin\n  have h : a = a,\n  { rw [mul_assoc],\n\n  rw [pow_mul],\nend\n\nDone."
        body, how = proof_text.recover_lean3(reply, NAME)
        lines = [l.strip() for l in body.splitlines()]
        self.assertEqual(lines[-2:], ["}", "end"])
        self.assertIn("unclosed_braces", how)

    def test_repetition_is_cut_and_comments_survive(self):
        reply = HEAD + "\nbegin\n  -- simplify\n" + "  simp only [add_comm],\n" * 12 + "end"
        body, how = proof_text.recover_lean3(reply, NAME)
        self.assertEqual(body.count("simp only [add_comm]"), 1)
        self.assertIn("-- simplify", body)
        self.assertIn("repetition_cut", how)

    def test_nothing_is_invented_for_lean4_prose_or_another_theorem(self):
        self.assertIsNone(proof_text.recover_lean3(HEAD + " by\n  omega", NAME))
        self.assertIsNone(proof_text.recover_lean3("theorem other : 1 = 1 :=\nbegin\n  refl\nend", NAME))
        self.assertIsNone(proof_text.recover_lean3("I think it is true.", NAME))

    def test_recovery_is_bounded(self):
        reply = HEAD + "\nbegin\n" + "".join(f"  have h{i} : {i} = {i} := rfl,\n" for i in range(500))
        body, how = proof_text.recover_lean3(reply, NAME)
        self.assertLessEqual(len(body.splitlines()), proof_text.MAX_RECOVER_LINES + 3)
        self.assertIn("cut_at_max_lines", how)


class ToolsAlone(unittest.TestCase):
    def test_whole_goal_tries_every_closer_on_the_bare_statement(self):
        seen = []
        def judge(text):
            seen.append(text.splitlines()[-1].strip())
            return {"verdict": "accept" if text.rstrip().endswith("omega") else "reject"}
        self.assertEqual(subgoals.whole_goal("theorem x : 1 + 1 = 2 := by", judge), "omega")
        self.assertEqual(seen, ["omega"])
        self.assertIsNone(subgoals.whole_goal("theorem x : 1 + 1 = 2 := by", lambda t: {"verdict": "reject"}))


class Replay(unittest.TestCase):
    PREFIX = HEAD.replace(":=", ":= by")

    def test_an_accepted_answer_stays_accepted_in_both_arms(self):
        # Codex 20261024T161801868685Z f6: run_chain discards a first accept, so the replay judges first
        row = {"id": 2, "target": NAME, "response": "```lean\n" + self.PREFIX + "\n  omega\n```", "verdict": "accept"}
        judge = lambda text: {"verdict": "accept", "output": ""}
        def chain(*a, **k):
            raise AssertionError("an accepted proof never reaches the chain")
        for arm in ("off", "on"):
            self.assertEqual(replay.replay_one(row, self.PREFIX, arm, judge, chain)["verdict"], "accept")

    def test_recovery_on_reaches_the_chain_where_off_cannot(self):
        row = {"id": 4, "target": NAME, "response": HEAD + "\nbegin\n  rw add_comm,\nend"}
        judge = lambda text: {"verdict": "reject", "output": "x.lean:2:2: error: nope"}
        chained = []
        chain = lambda proof, prefix, said: chained.append(proof) or {"c_verdict": "accept", "fixes": ["lean3"], "rep": {}}
        off = replay.replay_one(row, self.PREFIX, "off", judge, chain)
        on = replay.replay_one(row, self.PREFIX, "on", judge, chain)
        self.assertEqual((off["verdict"], off["reason"]), ("reject", "no proof extracted from reply"))
        self.assertEqual((on["verdict"], on["transforms"]), ("accept", ["lean3_begin"]))
        self.assertEqual(len(chained), 1)

    def test_report_counts_problems_on_the_report_half_only_and_names_both_sides(self):
        rep, tune = half_problem("report"), half_problem("tune")
        rows = [{"target_set": "s", "target": rep, "attempt_id": 1, "arm": "on", "verdict": "accept", "rung": "r"},
                {"target_set": "s", "target": rep, "attempt_id": 1, "arm": "off", "verdict": "reject", "rung": "r"},
                {"target_set": "s", "target": rep, "arm": "tools_alone", "verdict": "reject", "rung": "r"},
                {"target_set": "s", "target": tune, "attempt_id": 2, "arm": "on", "verdict": "accept", "rung": "r"}]
        cohort = [{"id": 1, "target_set": "s", "target": rep, "verdict": "reject", "rung": "r"},
                  {"id": 2, "target_set": "s", "target": tune, "verdict": "reject", "rung": "r"}]
        r = replay.report(rows, cohort)
        self.assertEqual(r["problems"], 1, "the tune-half problem is never counted")
        self.assertEqual((r["on"]["solved"], r["off"]["solved"], r["tools_alone"]["solved"]), (1, 0, 0))
        self.assertEqual((r["model_assisted_only"], r["tools_alone_only"]), (1, 0))

    def test_exposed_attempts_and_changed_statements_are_left_out(self):
        cohort = [{"id": 15335, "target_set": "s", "target": "a", "statement_sha": "x"},
                  {"id": 7, "target_set": "s", "target": "a", "statement_sha": "old"},
                  {"id": 9, "target_set": "s", "target": "a", "statement_sha": "x"}]
        keep, dropped = replay.eligible(cohort, lambda s, t: "x")
        self.assertEqual([r["id"] for r in keep], [9])
        self.assertEqual(dropped, {"exposed": [15335], "statement_changed": [7]})

    def test_results_are_fenced_from_every_try_reader(self):
        self.assertIn("replay", ledger_files.NOT_TRIES)


class ReportIntegrity(unittest.TestCase):
    """Codex 20261024T170221251251Z: exposure by problem, current results only, pending never counted as failure, one
    tools-alone owner per problem, per-rung intervals."""
    V = {"tools_hash": "t1", "lean_env": "l1"}

    def setUp(self):
        self.p, self.q = half_problem("report"), half_problem("report", "s2")
        self.cohort = [{"id": 1, "target_set": "s", "target": self.p, "verdict": "reject", "rung": "r"},
                       {"id": 3, "target_set": "s2", "target": self.q, "verdict": "reject", "rung": "r"}]

    def rows(self, *extra):
        base = [{"attempt_id": 1, "target_set": "s", "target": self.p, "arm": "off", "verdict": "reject", **self.V},
                {"attempt_id": 1, "target_set": "s", "target": self.p, "arm": "on", "verdict": "accept", **self.V},
                {"attempt_id": None, "target_set": "s", "target": self.p, "arm": "tools_alone", "verdict": "reject", **self.V}]
        return base + list(extra)

    def test_every_attempt_read_during_diagnosis_takes_its_problem_out(self):
        self.assertEqual(replay.EXPOSED, {15335, 15336, 15354})
        cohort = self.cohort + [{"id": 15336, "target_set": "s", "target": self.p, "verdict": "reject", "rung": "r"}]
        r = replay.report(self.rows(), cohort, **self.V)
        self.assertEqual(r["exposed_problems"], 1)
        self.assertNotIn(("s", self.p), r["complete"])

    def test_only_current_results_for_eligible_attempts_count(self):
        stale = {"attempt_id": 3, "target_set": "s2", "target": self.q, "arm": "on", "verdict": "accept",
                 "tools_hash": "old", "lean_env": "l1"}
        foreign = {"attempt_id": 99, "target_set": "s", "target": self.p, "arm": "off", "verdict": "accept", **self.V}
        r = replay.report(self.rows(stale, foreign), self.cohort, **self.V)
        self.assertEqual(r["off"]["solved"], 0, "attempt 99 is not in the eligible cohort")
        self.assertEqual(r["pending"], 1, "s2's only result is from older code: still pending")

    def test_pending_problems_are_named_never_counted_as_failures(self):
        r = replay.report(self.rows(), self.cohort, **self.V)
        self.assertEqual((r["problems"], r["pending"]), (1, 1))
        self.assertEqual(r["on"]["solved"], 1)
        r = replay.report([], self.cohort, **self.V)
        self.assertEqual((r["problems"], r["pending"], r["on"]["wilson95"]), (0, 2, None))
        self.assertIn("pending", replay.render(r))

    def test_tools_alone_has_one_owner_slice_per_problem(self):
        owners = {k for k in range(6) if replay.owns_baseline("s", self.p, k, 6)}
        self.assertEqual(len(owners), 1)

    def test_each_rung_has_its_own_interval(self):
        r = replay.report(self.rows(), self.cohort, **self.V)
        self.assertEqual(r["by_rung"]["r"]["on"]["solved"], 1)
        self.assertIsNotNone(r["by_rung"]["r"]["on"]["wilson95"])
