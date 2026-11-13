"""The worst-lane replay (2026-10-24): a frozen cohort of one lane's raw replies re-run with zero model calls through
extraction with and without Lean 3 recovery, the chain, and tools alone. No Lean here: stand-in judges."""
import sys
import unittest
import unittest.mock
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

class NoModelSetTests(unittest.TestCase):
    """The recorded no-model baseline (replay tools_alone), read as a versioned set (#574, Codex 20261109T032109853848Z)."""
    def ledger(self, rows):
        import json, tempfile
        d = Path(tempfile.mkdtemp())
        (d / "replay").mkdir()
        (d / "replay" / "results-1-0.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
        return d

    def row(self, t, v, run="1", env="e", tools="b6dddd8ade"):
        return {"arm": "tools_alone", "target_set": "s", "target": t, "verdict": v, "run_id": run, "lean_env": env,
                "tools_hash": tools, "ts": "2026-10-24T19:00:00+00:00"}

    def test_the_set_and_its_version(self):
        b = replay.no_model_set(self.ledger([self.row("a", "accept"), self.row("b", "reject"),
                                             {"arm": "off", "target_set": "s", "target": "c", "verdict": "accept"}]))
        self.assertEqual((b["set"], b["targets"]), ({("s", "a")}, 2))
        self.assertEqual((b["version"]["run_id"], b["version"]["date"]), ("1", "2026-10-24"))
        self.assertIn("grind", b["version"]["tactics"])

    def test_no_rows_is_an_error_never_an_empty_set(self):
        with self.assertRaises(ValueError):
            replay.no_model_set(self.ledger([]))

    def test_the_pinned_run_is_the_default_and_incomplete_is_not_a_reject(self):
        rows = [self.row("a", "accept"), self.row("b", "accept", run="2", tools="other"), self.row("c", "incomplete", run="2", tools="other")]
        with unittest.mock.patch.object(replay, "BASELINE_RUN", "2"):
            b = replay.no_model_set(self.ledger(rows))
        self.assertEqual((b["set"], b["targets"], b["incomplete"]), ({("s", "b")}, 2, 1))

    def test_mixed_versions_are_refused_unless_one_is_named(self):
        rows = [self.row("a", "accept"), self.row("b", "accept", run="2", tools="other")]
        with self.assertRaises(ValueError):
            replay.no_model_set(self.ledger(rows))
        self.assertEqual(replay.no_model_set(self.ledger(rows), run_id="2")["set"], {("s", "b")})


class BaselineSweepTests(unittest.TestCase):
    """The extended no-model baseline (#574): one Lean run per target holding every recipe, passes re-judged alone,
    a Lean timeout kept as incomplete (Codex 20261109T031816634913Z f3)."""
    TARGET = "import Mathlib\n\ntheorem t (a : ℝ) (h : 0 < a) : 0 < a * 2 := by\n  sorry\n"

    def test_the_recipes_keep_the_first_baseline_and_add_duotactics_table(self):
        r = replay.BASELINE_RECIPES
        self.assertEqual(len(r), len(set(r)))
        self.assertTrue(set(subgoals.AUTO_TACTICS) <= set(r))
        for t in ("ring", "field_simp; ring", "simp_all; linarith", "gcongr", "bound"):
            self.assertIn(t, r)

    def test_a_pass_is_judged_alone_and_a_timeout_is_incomplete(self):
        seen = {}
        def run_lean(text, timeout=180):
            seen["text"] = text
            return "", 1.0                                           # no messages: every recipe passes the filter
        judged = []
        def judge(text, timeout=300):
            judged.append(text)
            return {"verdict": "accept" if "nlinarith" in text.split(":= by")[-1] else "reject"}
        row = replay.baseline_one(self.TARGET, run_lean, judge, ["linarith", "nlinarith"])
        self.assertIn("theorem sb_goal_r1", seen["text"])
        self.assertEqual((row["verdict"], row["closer"]), ("accept", "nlinarith"))
        self.assertTrue(all(t.startswith("import Mathlib") and "theorem t " in t for t in judged), "judged as the target itself")
        row = replay.baseline_one(self.TARGET, lambda t, timeout=180: ("timeout after 300 s", 300.0), judge, ["linarith", "omega"])
        self.assertEqual((row["verdict"], row["closer"], row["unfinished"]), ("incomplete", None, ["linarith", "omega"]))
        real = lambda t, timeout=300: {"verdict": "reject", "reason": "timeout after 300s"}   # check.judge's own shape
        row = replay.baseline_one(self.TARGET, run_lean, real, ["linarith"])
        self.assertEqual(row["verdict"], "incomplete", "check.judge's timeout reject is a timeout (Codex f1)")
        kill = "killed (exit -9) under the 4000 MB memory limit"                                   # kumori #683, Codex 20261113T015106887824Z f2
        row = replay.baseline_one(self.TARGET, lambda t, timeout=180: (kill, 5.0), judge, ["linarith", "omega"])
        self.assertEqual((row["verdict"], row["unfinished"]), ("incomplete", ["linarith", "omega"]))
        row = replay.baseline_one(self.TARGET, run_lean, lambda t, timeout=300: {"verdict": "reject", "reason": kill}, ["linarith"])
        self.assertEqual(row["verdict"], "incomplete", "a check the memory limit killed is not a finished reject")
        row = replay.baseline_one(self.TARGET, run_lean, lambda t, timeout=300: {"verdict": "reject"}, ["linarith"])
        self.assertEqual(row["verdict"], "reject")

    def test_two_dispatches_make_one_version_and_retry_the_incomplete(self):
        """Codex f2 (20261109T042529567555Z): resume skipped incomplete targets and split runs across ids."""
        import json, tempfile, types
        root = Path(tempfile.mkdtemp())
        for t in ("a", "b"):
            (root / "targets" / "primer").mkdir(parents=True, exist_ok=True)
            (root / "targets" / "primer" / f"{t}.lean").write_text(self.TARGET.replace("theorem t ", f"theorem {t} "))
        for d in ("minif2f/test", "mil"):
            (root / "targets" / d).mkdir(parents=True, exist_ok=True)
        (root / "ledger" / "replay").mkdir(parents=True)
        verdicts = {"a": ["incomplete", "accept"], "b": ["reject"]}
        calls = []
        def one(text, run_lean, judge, first=None):
            t = "a" if "theorem a " in text else "b"
            calls.append(t)
            v = verdicts[t].pop(0)
            return {"verdict": v, "closer": "omega" if v == "accept" else None}
        args = types.SimpleNamespace(slice="0/1", max_minutes=0)
        with unittest.mock.patch.object(replay, "ROOT", root), unittest.mock.patch.object(replay, "REPLAY", root / "ledger" / "replay"), \
             unittest.mock.patch.object(replay, "baseline_one", one), unittest.mock.patch.object(replay, "versions", lambda: ("h", "e")), \
             unittest.mock.patch.dict("os.environ", {"GITHUB_RUN_ID": "1"}):
            replay.run_baseline(args)
            with unittest.mock.patch.dict("os.environ", {"GITHUB_RUN_ID": "2"}):
                replay.run_baseline(args)
        self.assertEqual(calls, ["a", "b", "a"], "the second dispatch asks only the incomplete target again")
        b = replay.no_model_set(root / "ledger", run_id=replay.BASELINE_V2_ID)
        self.assertEqual((b["set"], b["targets"], b["incomplete"]), ({("primer", "a")}, 2, 0))

    def test_the_last_baselines_closer_is_judged_first_and_slow_recipes_wait(self):
        batches = []
        def run_lean(text, timeout=180):
            batches.append(text.count("theorem sb_goal_r"))
            return "", 1.0
        judged = []
        judge = lambda t, timeout=300: judged.append(t.split("\n")[-1].strip()) or {"verdict": "accept" if "omega" in t else "reject"}
        row = replay.baseline_one(self.TARGET, run_lean, judge, ["linarith", "exact?", "omega"], first="omega")
        self.assertEqual((row["closer"], batches, judged), ("omega", [], ["omega"]), "no batch when the old closer still works")
        batches.clear(); judged.clear()
        row = replay.baseline_one(self.TARGET, run_lean, lambda t, timeout=300: {"verdict": "reject"}, ["linarith", "omega", "exact?"])
        self.assertEqual(batches, [2], "the fast pair in one batch; the slow one alone is judged, not batched")

class CohortReadTests(unittest.TestCase):
    """A second frozen cohort read per reply against its recorded verdict (#574, Codex 20261109T164835638082Z)."""
    def test_columns_are_separate_and_pending_is_not_a_failure(self):
        cohort = [{"id": i, "backend": "m3", "target_set": "s", "target": t, "verdict": v}
                  for i, t, v in ((1, "hard", "accept"), (2, "raw", "reject"), (3, "hard", "reject"),
                                  (4, "hard2", "reject"), (5, "easy", "reject"), (6, "hard", "reject"))]
        res = lambda i, arm, v, stage=None: {"cohort": "c", "attempt_id": i, "arm": arm, "verdict": v,
                                             **({"stage": stage} if stage else {})}
        results = [res(2, "off", "accept", "as_extracted"), res(2, "on", "accept", "as_extracted"),
                   res(3, "off", "accept", "chain"), res(3, "on", "accept", "chain"),
                   res(4, "off", "reject"), res(4, "on", "accept", "chain"),
                   res(5, "off", "accept", "chain"), res(5, "on", "accept", "chain"),
                   res(6, "off", "reject"),                                             # on arm not yet run
                   {**res(3, "off", "accept", "chain"), "cohort": "other"}]
        base = {"set": {("s", "easy")}, "tested": {("s", "easy"), ("s", "hard"), ("s", "hard2"), ("s", "raw")}, "unknown": set(),
                "version": {"run_id": "b2"}}
        d = replay.cohort_read(results, cohort, "c", base)["lanes"]["m3"]
        self.assertEqual((d["replies"], d["recorded_accept"], d["pending"]), (6, 1, 1))
        self.assertEqual((d["as_extracted"], d["chain"], d["recovery_extra"]), (1, 2, 1))
        self.assertEqual(d["targets_rescued_off"], [("s", "hard"), ("s", "hard2")], "a fresh raw accept is no rescue")
        self.assertEqual(d["targets_rescued_in"], 1)

    def test_only_one_code_and_lean_version_forms_a_pair(self):
        """Codex 20261109T171055036714Z f1: obsolete results stay pending, and arms of two versions never pair."""
        cohort = [{"id": 1, "backend": "m", "target_set": "s", "target": "t", "verdict": "reject"}]
        base = {"set": set(), "tested": {("s", "t")}, "unknown": set(), "version": {"run_id": "b"}}
        row = lambda arm, h: {"cohort": "c", "attempt_id": 1, "arm": arm, "verdict": "accept", "stage": "chain",
                              "tools_hash": h, "lean_env": "e"}
        old = replay.cohort_read([row("off", "old"), row("on", "old")], cohort, "c", base, "new", "e")["lanes"]["m"]
        self.assertEqual((old["pending"], old["chain"]), (1, 0))
        mixed = replay.cohort_read([row("off", "new"), row("on", "old")], cohort, "c", base, "new", "e")["lanes"]["m"]
        self.assertEqual(mixed["pending"], 1)
        same = replay.cohort_read([row("off", "new"), row("on", "new")], cohort, "c", base, "new", "e")["lanes"]["m"]
        self.assertEqual((same["pending"], same["chain"]), (0, 1))

