"""tools/lane_repair.py: a free lane writes a repair pass, selected on the tune half, reported once on the report
half, never credited for an accept the tools already had. Stand-in writer, runner and judge: no Lean, no network."""
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import lane_repair as lr


def row(i, target, kind="unknown_name", body="\n  trivial\n", verdict="reject"):
    return {"id": i, "target_set": "minif2f/test", "target": target, "failure_kind": kind, "verdict": verdict,
            "reason": "lean exit 1: 3:2: error: Unknown identifier `foo`",
            "response": f"```lean4\ntheorem {target} : True := by{body}```"}


def in_process_runner(code, items):
    """What the container does, in this process: tests only."""
    ns = {"__name__": "candidate"}
    exec(compile(code, "candidate.py", "exec"), ns)
    return {it["id"]: ns["repair"](it["proof"], it["lean_output"]) for it in items}


GOOD = "```python\ndef repair(proof, lean_output):\n    return proof.replace('foo', 'bar')\n```"
NOOP = "```python\ndef repair(proof, lean_output):\n    return proof\n```"
CRASH = "```python\ndef repair(proof, lean_output):\n    return 1 / 0\n```"


class Halves(unittest.TestCase):
    def test_examples_come_from_the_tune_half_only(self):
        cohort = [row(i, f"p{i}") for i in range(40)]
        ex = lr.examples(cohort, "unknown_name", lambda s, t: "tune" if int(t[1:]) % 2 else "report", n=8)
        self.assertEqual(len(ex), 8)
        self.assertTrue(all(int(e["target"][1:]) % 2 for e in ex))

    def test_only_rejects_the_tools_still_reject_are_scored(self):
        cohort = [row(1, "a"), row(2, "b"), row(3, "c", verdict="accept")]
        still = {1}                                       # 2 was turned by the chain already: never the pass's credit
        items = lr.items(cohort, "unknown_name", still, lambda s, t: "tune")
        self.assertEqual([it["id"] for it in items], [1])
        self.assertEqual(items[0]["proof"], "  trivial\n")


class Loop(unittest.TestCase):
    def setUp(self):
        self.cohort = [row(i, f"p{i}", body="\n  foo\n") for i in range(1, 13)]
        self.half = lambda s, t: "tune" if int(t[1:]) <= 6 else "report"
        self.judge = lambda text: {"verdict": "accept" if "bar" in text and "foo" not in text else "reject"}
        self.prefix = lambda s, t: "import Mathlib"

    def run_loop(self, replies, keep_at=3):
        it = iter(replies)
        return lr.run("unknown_name", lambda p: next(it), "lane-w", self.cohort, set(range(1, 13)), self.half,
                      in_process_runner, self.judge, self.prefix, rounds=len(replies), keep_at=keep_at)

    def test_a_pass_that_turns_enough_tune_rejects_is_kept_and_run_once_on_the_report_half(self):
        rows = self.run_loop([GOOD])
        (r,) = rows
        self.assertEqual((r["writer"], r["tune_turned"], r["tune_n"], r["kept"]), ("lane-w", 6, 6, True))
        self.assertEqual((r["report_turned"], r["report_n"]), (6, 6))
        self.assertIn("wilson95", r)
        self.assertEqual((r["report_problems_turned"], r["report_problems"]), (6, 6))
        self.assertEqual(len(r["pass_sha"]), 64)

    def test_the_interval_counts_problems_not_attempts(self):
        its = [{"id": 1, "target_set": "s", "target": "a", "proof": "x", "lean_output": ""},
               {"id": 2, "target_set": "s", "target": "a", "proof": "y", "lean_output": ""},
               {"id": 3, "target_set": "s", "target": "b", "proof": "z", "lean_output": ""}]
        r = lr.half_result(its, turned=[1, 2], pending=[])
        self.assertEqual((r["turned"], r["n"], r["problems_turned"], r["problems"]), (2, 3, 1, 2))

    def test_a_cut_off_tune_run_is_pending_and_decides_nothing(self):
        it = iter([GOOD])
        rows = lr.run("unknown_name", lambda p: next(it), "lane-w", self.cohort, set(range(1, 13)), self.half,
                      in_process_runner, self.judge, self.prefix, rounds=1, max_minutes=-1)
        self.assertEqual(rows[0].get("pending"), "deadline after 0 asks")

    def test_the_output_protocol_refuses_extra_missing_or_oversized_proofs(self):
        its = [{"id": 1, "target_set": "s", "target": "a", "proof": "x", "lean_output": ""}]
        self.assertEqual(lr.validate_output(its, {1: "ok"}), {1: "ok"})
        for bad in ({1: "ok", 2: "extra"}, {}, {1: 5}, {1: "p" * (lr.MAX_PROOF_CHARS + 1)}):
            with self.assertRaises(ValueError):
                lr.validate_output(its, bad)

    def test_a_miss_is_recorded_and_never_sees_the_report_half(self):
        (r,) = self.run_loop([NOOP])
        self.assertEqual((r["error"], r["kept"]), ("screen: no change on any example", False))
        self.assertNotIn("report_turned", r)

    def test_a_crash_goes_back_to_the_writer_with_its_traceback(self):
        (r,) = self.run_loop([CRASH, GOOD])
        self.assertEqual((r["repair_asks"], r["kept"]), (1, True))
        self.assertIn("ZeroDivisionError", r["screen_errors"][0])

    def test_the_brief_names_the_contract_and_the_pass_to_beat_and_no_report_row(self):
        text = lr.brief("unknown_name", lr.examples(self.cohort, "unknown_name", self.half, n=8), "def names(): ...")
        self.assertIn("def repair(proof: str, lean_output: str) -> str", text)
        self.assertIn("def names(): ...", text)
        for i in range(7, 13):
            self.assertNotIn(f"p{i}", text)


if __name__ == "__main__":
    unittest.main()
