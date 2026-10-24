"""The weekly failure triage (2026-10-24): answered rejects per lane and class, candidates ranked across lanes.
Codex 20261024T192423729277Z and 20261024T192633227087Z shaped it. No Lean, no network."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import triage

W = "2026-10-20T00:00:00+00:00"          # ISO week 2026-W43


def rej(lane, kind, n=1, field="backend", ts=W, target="p"):
    return [{field: lane, "verdict": "reject", "failure_kind": kind, "ts": ts, "target_set": "s", "target": f"{target}{i}",
             "statement_sha": "x", "mode": "ladder-x3", "try_mode": "cold"} for i in range(n)]


class Reader(unittest.TestCase):
    def test_lane_comes_from_backend_or_lane_and_labels_never_vanish(self):
        rows = rej("a", "tactic_failed") + rej("fc", "unknown_name", field="lane") + rej("b", None) \
            + [{"verdict": "reject", "failure_kind": "x", "ts": W, "target": "q"}] \
            + [{"backend": "a", "verdict": "error", "failure_kind": "lane_error", "ts": W, "target": "q"},
               {"backend": "a", "verdict": "reject", "try_mode": "fixer+loop", "failure_kind": "x", "ts": W, "target": "q"}]
        got = triage.answered_rejects(rows)
        self.assertEqual(sorted((r["lane"], r["class"]) for r in got),
                         [("a", "tactic_failed"), ("b", "unclassified"), ("fc", "unknown_name"), ("unattributed", "x")])


class Queue(unittest.TestCase):
    def test_per_lane_bar_or_top_five_and_ranked_by_cross_lane_demand(self):
        rows = (rej("a", "no_fence", 60) + rej("a", "tactic_failed", 50) + rej("b", "tactic_failed", 40)
                + rej("b", "lean3_syntax", 70) + rej("c", "k1", 1) + rej("c", "k2", 1) + rej("c", "k3", 1))
        q = triage.queue(triage.answered_rejects(rows), week=(2026, 43))
        names = [c["class"] for c in q["candidates"]]
        self.assertEqual(names[:3], ["tactic_failed", "lean3_syntax", "no_fence"])     # 90, 70, 60 across lanes
        self.assertIn("k1", names, "top five by cross-lane total, though under every lane's bar")
        tf = q["candidates"][0]
        self.assertEqual((tf["total"], tf["week"], sorted(tf["lanes"])), (90, 90, ["a", "b"]))
        self.assertEqual(tf["passes_lane_bar"], ["a"])             # a: 50 of 110 (45%); b: 40 of 110 (36%)
        self.assertEqual(q["unclassified"], 0)

    def test_frozen_replies_change_no_rank(self):
        rows = triage.answered_rejects(rej("a", "no_fence", 120) + rej("b", "tactic_failed", 100))
        before = [c["class"] for c in triage.queue(rows, week=(2026, 43))["candidates"]]
        cohort = [{"id": i, "verdict": "reject", "failure_kind": "no_fence", "target_set": "s", "target": f"p{i}",
                   "attempt_no": None, "response": "theorem p := begin\n  simp,\nend", "run_id": "None",
                   "created_at": W} for i in range(5)]
        after = triage.queue(rows, week=(2026, 43), cohorts={"a": cohort})
        self.assertEqual([c["class"] for c in after["candidates"]], before)
        nf = next(c for c in after["candidates"] if c["class"] == "no_fence")
        self.assertEqual(nf["refined"]["covered"], 5)


class Signatures(unittest.TestCase):
    def test_one_primary_signature_each_truncation_a_flag_and_totals_reconcile(self):
        replies = ["theorem t : 1 = 1 :=\nbegin\n  refl,\nend",
                   "theorem t : 1 = 1 :=\nbegin\n  rw [a, b, c",
                   "```lean\ntheorem t : 1 = 1 := by\n  rfl\n```",
                   "theorem t : 1 = 1 := by\n  rfl",
                   "I believe this holds."]
        sigs = [triage.signature(r, "t") for r in replies]
        self.assertEqual([s["primary"] for s in sigs],
                         ["lean3_body", "lean3_body", "fenced_lean4", "unfenced_lean4", "prose"])
        self.assertEqual([s["truncated"] for s in sigs], [False, True, False, False, False])

    def test_cohort_rows_join_by_attempt_and_db_only_rows_are_apart(self):
        cohort = [{"id": i, "verdict": "reject", "failure_kind": "no_fence", "response": "x", "target_set": "s",
                   "target": "p", "attempt_no": 1, "run_id": run, "created_at": W}
                  for i, run in ((1, "r1"), (2, "r1"), (3, "db"))]
        ledger = [{"lane": "a", "class": "no_fence", "run_id": "r1", "target_set": "s", "target": "p", "attempt_no": 1,
                   "ts": W}] * 2
        ref = triage.refine("a", "no_fence", cohort, ledger, cutoff="2026-10-26")
        self.assertEqual((ref["covered"], ref["db_only"]), (2, 1), "two replies to one problem are two attempts")


class Page(unittest.TestCase):
    def test_written_once_with_its_input_boundary(self):
        with tempfile.TemporaryDirectory() as d:
            q = triage.queue(triage.answered_rejects(rej("a", "x", 3)), week=(2026, 43))
            p = triage.write_page(q, Path(d), rev="abc", classifier="h1")
            self.assertTrue(p.name.endswith("2026-W43-triage.md"))
            meta = json.loads(p.with_suffix(".json").read_text())
            self.assertEqual((meta["ledger_rev"], meta["classifier"], meta["cutoff"]), ("abc", "h1", "2026-10-26"))
            self.assertIsNone(triage.write_page(q, Path(d), rev="def", classifier="h2"), "never rewritten")


class JoinFixes(unittest.TestCase):
    """Codex 20261024T193402083246Z: a real attempt join under the cutoff, the fallback bounded to its declaration, and
    the page showing what the JSON knows."""
    def ledger(self, n, run="r1", target="p", attempt=1):
        return [{"run_id": run, "target_set": "s", "target": target, "attempt_no": attempt, "class": "no_fence",
                 "ts": W, "lane": "a"} for _ in range(n)]

    def cohort_row(self, i, run="r1", target="p", attempt=1, ts=W):
        return {"id": i, "verdict": "reject", "failure_kind": "no_fence", "response": "x", "target_set": "s",
                "target": target, "attempt_no": attempt, "run_id": run, "created_at": ts}

    def test_coverage_never_exceeds_the_ledger_attempts_it_matches(self):
        cohort = [self.cohort_row(1), self.cohort_row(2)]
        ref = triage.refine("a", "no_fence", cohort, self.ledger(1), cutoff="2026-10-26")
        self.assertEqual((ref["covered"], ref["db_only"]), (1, 1), "two replies, one ledger attempt: 1 covered")

    def test_cohort_rows_after_the_cutoff_are_left_out(self):
        cohort = [self.cohort_row(1, ts="2026-10-30T00:00:00+00:00")]
        ref = triage.refine("a", "no_fence", cohort, self.ledger(1), cutoff="2026-10-26")
        self.assertEqual((ref["covered"], ref["db_only"], ref["after_cutoff"]), (0, 0, 1))

    def test_the_lean3_fallback_stays_inside_the_target_declaration(self):
        reply = "theorem t : 1 = 1 := by\n  rfl\n\ntheorem other : 2 = 2 :=\nbegin\n  refl"
        self.assertEqual(triage.signature(reply, "t")["primary"], "unfenced_lean4")

    def test_the_page_shows_lane_db_only_and_truncated(self):
        q = {"week": [2026, 43], "cutoff": "2026-10-26", "rejects": 1, "lanes": 1, "unclassified": 0, "unattributed": 0,
             "candidates": [{"class": "no_fence", "total": 10, "week": 1, "lanes": {"a": 10}, "passes_lane_bar": [],
                             "in_top": True, "existing_tool": None, "recoverability": "unknown",
                             "refined": {"covered": 3, "of": 10, "by_lane": [{"lane": "a", "covered": 3, "db_only": 2,
                                                                               "signatures": {"lean3_body": 3},
                                                                               "truncated": 1, "after_cutoff": 0}]}}]}
        page = triage.render(q)
        self.assertIn("a: 3 of 10", page)
        self.assertIn("2 database-only", page)
        self.assertIn("1 truncated", page)
