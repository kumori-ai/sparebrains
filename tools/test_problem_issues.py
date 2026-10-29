"""Issue threads, rendered offline from a fixture dossier: what the bot posts and what it never posts."""
import sys
import tempfile
import json
import unittest
from datetime import datetime, timezone
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
    def test_posts_the_school_report_and_the_actions_runs(self):
        import daily_report
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "ledger" / "s" / "1.jsonl"
            f.parent.mkdir(parents=True)
            f.write_text("".join(json.dumps(dict(ts=ts, target_set="s", target=t, backend=b, verdict=v, mode=m, quality_tier="low")) + "\n"
                                 for ts, t, b, v, m in [("2026-10-16T10:00:00+00:00", "a", "x", "accept", "relay"),
                                                        ("2026-10-17T10:00:00+00:00", "a", "x", "accept", "relay"),
                                                        ("2026-10-17T11:00:00+00:00", "b", "y", "accept", "prover"),
                                                        ("2026-10-17T12:00:00+00:00", "c", "y", "reject", "prover"),
                                                        ("2026-10-17T13:00:00+00:00", "c", "y", "error", "relay")]))
            report = daily_report.build(Path(tmp) / "ledger", datetime(2026, 10, 17, 22, 0, tzinfo=timezone.utc))
        runs = [dict(name="schedule", path=".github/workflows/attempt.yml", conclusion="success"),
                dict(name="workflow_dispatch", path=".github/workflows/attempt.yml", conclusion="success"),
                dict(name="prover", path=".github/workflows/prover.yml", conclusion="failure"),
                dict(name="bench", path=".github/workflows/bench.yml", conclusion="skipped")]
        text = pi.daily_log(report, runs)
        self.assertTrue(text.startswith(pi.LOG_MARKER))
        self.assertIn("**1 first-time solves**, 2 accepts from 3 answered tries by 2 lanes on 3 problems", text)
        self.assertIn("first solve: `s/b` by y (low, prover)", text)                 # s/a was solved before the window
        self.assertNotIn("`s/a`", text)
        self.assertIn("**GitHub Actions runs:** attempt 2 success; prover 1 failure\n", text)   # by workflow file, skipped left out
        self.assertIn("kumori_agents.md", text)


class FakeGitHub:
    """Records writes; POST returns a comment with an id so the daily comment can be found again."""
    def __init__(self):
        self.writes, self.next_id = [], 100

    def write(self, method, path, data=None):
        self.writes.append((method, path, data))
        if method == "POST":
            self.next_id += 1
            return {"id": self.next_id, "user": {"type": "Bot"}, "body": data["body"]}
        return {}


class AiwarsRulesTests(unittest.TestCase):
    """The 2026-10-18 r/aiwars review: credit every source, call nothing 'open problem' that people solved long
    ago, and never flood a thread's watchers."""

    def test_threads_and_solves_credit_the_source_and_say_people_solved_it(self):
        title, body = pi.render(D)
        self.assertTrue(title.startswith("Open to our free pool:"))
        self.assertNotIn("Open problem", title + body)
        self.assertIn("Mathematics in Lean by Jeremy Avigad and Patrick Massot", body)
        self.assertIn("People solved it long ago", body)
        amc = pi.credit("minif2f/test", "amc12a_2020_p7")          # the real target_set carries its split
        self.assertIn("AMC 12", amc)
        self.assertIn("miniF2F (OpenAI, 2021", amc)
        rows = [dict(run_id="9", target_set="minif2f/test", target="mathd_algebra_17", backend="y", attempt_no=1,
                     try_mode="prover", verdict="accept", reason="ok")]
        solved = dict(pi.digest("9", rows))["minif2f/test/mathd_algebra_17"]
        self.assertIn("MATH dataset", solved)

    def test_one_comment_a_day_edited_in_place(self):
        gh, thread = FakeGitHub(), []
        a = pi.post_daily(gh, 7, "run one\n\n" + pi.PITCH, thread, day="2026-10-18")
        b = pi.post_daily(gh, 7, "run two\n\n" + pi.PITCH, thread, day="2026-10-18")
        self.assertEqual((a, b), ("posted", "edited"))
        self.assertEqual([m for m, _, _ in gh.writes], ["POST", "PATCH"])
        final = gh.writes[-1][2]["body"]
        self.assertTrue(final.startswith("<!-- sparebrains:day 2026-10-18 -->"))
        self.assertIn("run one", final)
        self.assertIn("run two", final)
        self.assertEqual(final.count(pi.PITCH), 1)                    # the pitch once, not once per run
        self.assertEqual(pi.post_daily(gh, 7, "run three", thread, day="2026-10-19"), "posted")   # a new day

    def test_a_full_day_comment_starts_a_second_one(self):
        gh, thread = FakeGitHub(), []
        pi.post_daily(gh, 7, "x" * (pi.DAY_CAP - 1000), thread, day="2026-10-18")
        self.assertEqual(pi.post_daily(gh, 7, "y" * 2000, thread, day="2026-10-18"), "posted")

    def test_runs_in_the_daily_comment_still_count_as_reported(self):
        gh, thread = FakeGitHub(), []
        (_, text), = pi.digest("9", [dict(run_id="9", target_set="mil", target="a", backend="x", attempt_no=1,
                                          try_mode="relay", verdict="reject", reason="r")])
        pi.post_daily(gh, 7, text, thread, day="2026-10-18")
        self.assertIn("9", pi.digested_runs(thread))                  # so --catchup never posts it twice


class DailyFromMain(unittest.TestCase):
    """--daily through main(): the branch that posts the log, with GitHub, the relay and the report faked.
    (2026-10-29: ten Actions runs failed on a NameError here that no unit test of daily_log could see.)"""
    class GH:
        def __init__(self, token):
            self.writes = []

        def call(self, method, path, data=None):
            if path.startswith("/actions/runs"):
                return {"workflow_runs": [{"name": "attempt", "path": ".github/workflows/attempt.yml", "conclusion": "success"}]}
            return [{"number": 5, "body": pi.LOG_MARKER + " x"}]          # the open log issue

        def problem_issues(self):
            return {}

        def comments(self, number):
            return []

        def write(self, method, path, data=None):
            self.writes.append((method, path, data))
            return {"number": 5, "id": 1}

    def test_daily_posts_the_report_with_the_actions_line(self):
        from unittest import mock
        gh_box = []
        make = lambda token: gh_box.append(self.GH(token)) or gh_box[-1]
        report = {"day": "2026-10-29", "hours": 24}
        with mock.patch.object(pi, "GitHub", make), mock.patch.object(pi.relay, "fetch_json", return_value={"open": []}), \
             mock.patch.object(pi.daily_report, "build", return_value=report), \
             mock.patch.object(pi.daily_report, "render", return_value="report text"), \
             mock.patch.dict("os.environ", {"GH_TOKEN": "t"}), mock.patch.object(sys, "argv", ["problem_issues.py", "--daily"]):
            self.assertEqual(pi.main(), 0)
        (method, path, data), = gh_box[0].writes
        self.assertEqual((method, path), ("POST", "/issues/5/comments"))
        self.assertIn("report text", data["body"])
        self.assertIn("**GitHub Actions runs:** attempt 1 success", data["body"])


class GateNotes(unittest.TestCase):
    def test_status_checks_share_one_comment_a_day(self):
        gh, thread = FakeGitHub(), []
        pi.post_daily(gh, 23, "Prover check 1", thread, day="2026-10-18")
        pi.post_daily(gh, 23, "Prover check 2", thread, day="2026-10-18")
        self.assertEqual([m for m, _, _ in gh.writes], ["POST", "PATCH"])


if __name__ == "__main__":
    unittest.main()
