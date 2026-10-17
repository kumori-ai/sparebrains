"""Issue threads, rendered offline from a fixture dossier: what the bot posts and what it never posts."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import problem_issues as pi

D = dict(target_set="mil", target="mil_c05_s01_ex03", rung="mil", rung_label="textbook basics", solved=False,
         answered=114, lanes_tried=40, source="https://github.com/kumori-ai/sparebrains/blob/main/targets/mil/mil_c05_s01_ex03.lean",
         statement=None, failures=[dict(kind="unsolved_goals", n=10, lanes=6)], unknown_names=[["Nat.fake", 2], ["h", 5], ["x.val", 3]],
         near_misses=[dict(id=47348, backend="groq-gptoss", try_mode="relay", failure_kind="unsolved_goals",
                           proof="  intro h", lean_output="/home/runner/w/.lake/attempts/x.lean:4:107: error: unsolved goals")],
         thread=[])


class RenderTests(unittest.TestCase):
    def test_body_opens_with_the_marker_and_carries_the_pack(self):
        title, body = pi.render(D, order=1)
        self.assertTrue(body.startswith("<!-- sparebrains:problem mil/mil_c05_s01_ex03 -->"))
        self.assertIn("number 1 in the", body)
        self.assertIn("Prompt pack", body)
        self.assertIn("theorem mil_c05_s01_ex03", body)          # the statement, read from targets/
        self.assertIn("`Nat.fake`", body)
        self.assertNotIn("`h`", body)                            # a local name is not an invented library name
        self.assertNotIn("x.val", body)
        self.assertNotIn("/home/runner", body)
        self.assertIn("mil_c05_s01_ex03", title)

    def test_reference_proof_never_appears(self):
        ref = (pi.ROOT / "targets/mil/reference/mil_c05_s01_ex03.lean").read_text()
        _, body = pi.render(D)
        proof = ref.split(":= by", 1)[1].strip()
        self.assertNotIn(proof[:60], body)

    def test_a_solved_problem_is_never_rendered(self):
        with self.assertRaises(ValueError):
            pi.render(dict(D, solved=True))


class DigestTests(unittest.TestCase):
    def test_one_comment_per_problem_and_every_try_this_run(self):
        rows = [dict(run_id="9", target_set="mil", target="a", backend="x", attempt_no=1, try_mode="relay", verdict="reject", reason="unsolved goals"),
                dict(run_id="9", target_set="mil", target="a", backend="y", attempt_no=1, try_mode="relay", verdict="accept", reason="ok"),
                dict(run_id="9", target_set="mil", target="b", backend="x", attempt_no=1, try_mode="cold", verdict="reject", reason="cold row"),
                dict(run_id="8", target_set="mil", target="a", backend="z", attempt_no=1, try_mode="relay", verdict="reject", reason="old run")]
        out = dict(pi.digest("9", rows))
        self.assertEqual(sorted(out), ["mil/a", "mil/b"])          # every try on a problem, any mode, failures too
        self.assertIn("2 tries, 2 answers, 1 accepted", out["mil/a"])
        self.assertIn("cold row", out["mil/b"])
        self.assertIn("| `unknown` | `x` |", out["mil/b"])          # a row with no model says so rather than guessing
        self.assertIn("**Solved.**", out["mil/a"])
        self.assertNotIn("old run", out["mil/a"])


class QuoteReplyTests(unittest.TestCase):
    def test_a_thread_assisted_run_opens_by_quoting_the_comment_it_read(self):
        rows = [dict(run_id="9", target_set="mil", target="a", backend="x", attempt_no=1, try_mode="relay+thread",
                     comment_ids=[77], verdict="reject", reason="type mismatch"),
                dict(run_id="9", target_set="mil", target="a", backend="y", attempt_no=1, try_mode="relay+thread",
                     comment_ids=[77], verdict="reject", reason="unsolved goals")]
        text = dict(pi.digest("9", rows, {77: ("tillo13", "Idea: take logs\nof both sides")}))["mil/a"]
        self.assertTrue(text.split("\n", 1)[1].startswith("> **@tillo13** wrote:\n> Idea: take logs\n> of both sides"))
        self.assertIn("2 of this run's answers came from models that read the comment above", text)

    def test_a_run_that_read_no_comment_quotes_nothing(self):
        rows = [dict(run_id="9", target_set="mil", target="a", backend="x", attempt_no=1, try_mode="relay", verdict="reject", reason="r")]
        self.assertNotIn("wrote:", dict(pi.digest("9", rows, {}))["mil/a"])


class RefillTests(unittest.TestCase):
    """Keep N threads open: the next unsolved problems in the order, never a closed or existing one."""
    class GH:
        def __init__(self):
            self.posted = []

        def call(self, method, path, data=None):
            self.posted.append(data["title"])
            return {"number": 100 + len(self.posted), "html_url": "u", "state": "open"}

    def targets(self, *names):
        return [{"target_set": "s", "target": n} for n in names]

    def run_refill(self, issues, names, solved=(), n=5):
        gh = self.GH()
        fetch = lambda ts, t: {"solved": t in solved}
        opened = pi.refill(gh, issues, self.targets(*names), fetch, n, render_fn=lambda d, o: ("t", "b"))
        return opened, gh

    def test_tops_up_to_n_in_order_skipping_existing_closed_and_solved(self):
        issues = {"s/a": {"state": "open"}, "s/b": {"state": "open"}, "s/c": {"state": "closed"}}
        opened, _ = self.run_refill(issues, ["a", "b", "c", "d", "e", "f", "g"], solved=("d",))
        self.assertEqual(opened, ["s/e", "s/f", "s/g"])

    def test_nothing_opens_when_n_are_already_open(self):
        issues = {f"s/{x}": {"state": "open"} for x in "abcde"}
        opened, gh = self.run_refill(issues, ["f", "g"])
        self.assertEqual((opened, gh.posted), ([], []))

    def test_never_more_than_n_even_with_a_long_order(self):
        opened, _ = self.run_refill({}, [str(i) for i in range(50)], n=5)
        self.assertEqual(len(opened), 5)

    def test_max_new_paces_a_large_n_across_runs(self):
        gh = self.GH()
        opened = pi.refill(gh, {}, self.targets(*[str(i) for i in range(50)]), lambda ts, t: {"solved": False}, 1000,
                           render_fn=lambda d, o: ("t", "b"), max_new=25)
        self.assertEqual(len(opened), 25)


class CatchupTests(unittest.TestCase):
    """Every judged try reaches its thread once, whether or not GitHub fired the run's workflow_run event."""
    BOT, PERSON = {"type": "Bot"}, {"type": "User"}

    def test_reported_runs_come_from_the_marker_and_the_older_heading_in_bot_comments_only(self):
        comments = [dict(user=self.BOT, body="<!-- sparebrains:digest run=11 -->\n**Run [11](x)**"),
                    dict(user=self.BOT, body="**Run [10](https://sparebrains.kumori.ai/runs/10)** (relay): 3 tries"),
                    dict(user=self.PERSON, body="<!-- sparebrains:digest run=12 -->")]
        self.assertEqual(pi.digested_runs(comments), {"10", "11"})

    def test_pending_runs_are_unreported_after_the_thread_opened_any_mode_oldest_first(self):
        rows = [dict(run_id="3", ts="2026-10-17T05:00", verdict="reject", try_mode="prover"),
                dict(run_id="2", ts="2026-10-17T04:00", verdict="accept", try_mode="fixer+loop"),
                dict(run_id="1", ts="2026-10-16T00:00", verdict="reject"),         # before the thread opened
                dict(run_id="4", ts="2026-10-17T06:00", verdict="reject"),         # already reported
                dict(run_id="5", ts="2026-10-17T07:00", verdict="skipped")]        # never judged
        self.assertEqual(pi.pending_runs(rows, "2026-10-17T00:00", {"4"}), ["2", "3"])

    def test_every_digest_carries_its_run_marker_and_the_pitch(self):
        rows = [dict(run_id="9", target_set="mil", target="a", backend="x", attempt_no=1, verdict="reject", reason="r"),
                dict(run_id="9", target_set="mil", target="b", backend="x", attempt_no=1, verdict="accept", reason="ok")]
        out = dict(pi.digest("9", rows))
        self.assertTrue(out["mil/a"].startswith("<!-- sparebrains:digest run=9 -->"))
        for text in out.values():                                  # solved or not, every post points at kumori_agents.md
            self.assertIn("kumori_agents.md", text)


class LedgerDayTests(unittest.TestCase):
    def test_day_is_found_whether_or_not_ts_leads_the_row(self):
        self.assertEqual(pi.row_day('{"ts": "2026-10-17T22:08:00+00:00", "run_id": "1"}'), "2026-10-17")
        self.assertEqual(pi.row_day('{"run_id": "volunteer-6241938187", "ts": "2026-10-17T22:08:00+00:00"}'), "2026-10-17")
        self.assertEqual(pi.row_day('{"run_id": "x"}'), "")


class DailyLogTests(unittest.TestCase):
    def test_counts_first_time_solves_and_actions_runs(self):
        rows = [dict(target_set="s", target="a", backend="x", verdict="accept", try_mode="relay"),
                dict(target_set="s", target="b", backend="y", verdict="accept", try_mode="prover"),
                dict(target_set="s", target="c", backend="y", verdict="reject", try_mode="prover"),
                dict(target_set="s", target="c", backend="y", verdict="error", try_mode="relay")]
        runs = [dict(name="schedule", path=".github/workflows/attempt.yml", conclusion="success"),
                dict(name="workflow_dispatch", path=".github/workflows/attempt.yml", conclusion="success"),
                dict(name="prover", path=".github/workflows/prover.yml", conclusion="failure"),
                dict(name="bench", path=".github/workflows/bench.yml", conclusion="skipped")]
        text = pi.daily_log(rows, {"s/a"}, runs, "2026-10-17")
        self.assertTrue(text.startswith(pi.LOG_MARKER))
        self.assertIn("4 tries judged by the Lean kernel, 3 answered, **2 accepted**, by 2 lanes on 3 problems", text)
        self.assertIn("**First-time solves:** [`s/b`]", text)                 # s/a was solved before the window
        self.assertNotIn("`s/a`]", text)
        self.assertIn("| `prover` | 2 | 1 |", text)
        self.assertIn("**GitHub Actions runs:** attempt 2 success; prover 1 failure\n", text)   # by workflow file, skipped left out
        self.assertIn("kumori_agents.md", text)


if __name__ == "__main__":
    unittest.main()
