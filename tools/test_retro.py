"""tools/retro.py: the weekly retro reads only the ledger, counts a closed ISO week, names first-time solves and
the stop reason that grew, and writes the same bytes on a rerun. No network."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import retro


def row(ts, target, verdict, mode="ladder-x3", stopped=None, target_set="minif2f/test"):
    r = {"ts": ts, "target": target, "target_set": target_set, "verdict": verdict, "mode": mode}
    if stopped:                                      # where the ledger keeps it (10,531 rows as of 2026-10-22)
        r["tools"] = {"subgoals": {"stopped": stopped}}
    return r


ROWS = [
    row("2026-10-07T10:00:00+00:00", "a", "accept"),                           # week 41: a solved
    row("2026-10-08T10:00:00+00:00", "b", "reject", stopped="1 step(s) left for a model"),
    row("2026-10-13T10:00:00+00:00", "a", "accept", mode="relay"),            # week 42: a again, not first-time
    row("2026-10-14T10:00:00+00:00", "c", "accept", mode="prover"),           # week 42: c first-time
    row("2026-10-14T11:00:00+00:00", "b", "reject", stopped="1 step(s) left for a model"),
    row("2026-10-15T11:00:00+00:00", "b", "reject", stopped="no step of the proof survived"),
    row("2026-10-15T12:00:00+00:00", "b", "reject", stopped="no step of the proof survived"),
    row("2026-10-16T12:00:00+00:00", "d", "skipped"),                          # not a try
    row("2026-10-20T12:00:00+00:00", "e", "accept"),                           # week 43: still open, not reported
]


class Retro(unittest.TestCase):
    def test_the_last_closed_week_is_the_one_before_today(self):
        self.assertEqual(retro.last_closed_week("2026-10-22"), (2026, 42))
        self.assertEqual(retro.last_closed_week("2026-10-19"), (2026, 42))   # a Monday: last week just closed

    def test_tries_and_accepts_by_mode_count_only_that_week_and_skip_skipped(self):
        w = retro.summarize(ROWS, (2026, 42))
        self.assertEqual(w["modes"], {"relay": [1, 1], "prover": [1, 1], "ladder-x3": [3, 0]})

    def test_a_first_time_solve_is_a_targets_first_accept_ever(self):
        self.assertEqual(retro.summarize(ROWS, (2026, 42))["first_time"], [("minif2f/test", "c", "prover")])

    def test_the_stop_reasons_show_this_week_last_week_and_the_one_that_grew(self):
        w = retro.summarize(ROWS, (2026, 42))
        self.assertEqual(w["stops"], [("no step of the proof survived", 2, 0), ("1 step(s) left for a model", 1, 1)])
        self.assertEqual(w["grew"], "no step of the proof survived")

    def test_the_page_is_the_same_bytes_on_a_rerun_and_has_no_run_time(self):
        a, b = retro.render(retro.summarize(ROWS, (2026, 42))), retro.render(retro.summarize(list(ROWS), (2026, 42)))
        self.assertEqual(a, b)
        self.assertIn("2026-W42 (2026-10-12 to 2026-10-18)", a)
        self.assertIn("minif2f/test c", a)

    def test_rows_are_read_from_every_ledger_file_that_has_them(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "minif2f" / "test").mkdir(parents=True)
            (root / "minif2f" / "test" / "1.jsonl").write_text("\n".join(json.dumps(r) for r in ROWS[:3]) + "\n")
            (root / "openproblems").mkdir()
            (root / "openproblems" / "evolve-1.jsonl").write_text(json.dumps({"at": "x", "round": 1}) + "\n")
            (root / "bad.jsonl").write_text("{not json\n")
            self.assertEqual(len(retro.load(root)), 3)

    def test_an_empty_ledger_is_an_error_not_an_empty_week(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(SystemExit):
                retro.main(["--ledger", d, "--out", str(Path(d) / "retro"), "--today", "2026-10-22"])


if __name__ == "__main__":
    unittest.main()
