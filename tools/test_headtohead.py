"""The head-to-head (tools/headtohead.py): a stand-in model and judge, so these test the fairness rules, not Lean."""
import sys, unittest
from pathlib import Path
from unittest import mock

sys.path[:0] = [str(Path(__file__).resolve().parent)]
import decompose, headtohead as h

TARGET = "import Mathlib\n\nopen Real\n\ntheorem t1 (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by\n  sorry\n"


def answer(body):
    return f"```lean4\ntheorem t1 (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by\n{body}```"


class Fairness(unittest.TestCase):
    def test_the_set_is_fixed_by_the_seed_not_by_results(self):
        targets = {"open": [{"target_set": "s", "target": f"o{i}", "order": 9 - i} for i in range(5)],
                   "solved": [{"target_set": "s", "target": f"d{i}", "rung": r} for i, r in
                              enumerate(["aime", "primer", "imo", "math-L1", "custom"])]}
        a = h.pick(targets, 2, 2, lambda t: True)
        self.assertEqual(a, h.pick(targets, 2, 2, lambda t: True))
        self.assertEqual([t["target"] for t in a[:2]], ["o4", "o3"])            # the open list's order
        self.assertTrue(all(t["rung"] in h.HARD_RUNGS for t in a[2:]))           # primer and L1 never picked
        self.assertEqual([t["status"] for t in a], ["open", "open", "solved", "solved"])

    def test_slices_split_the_open_list_by_name_whatever_is_solved_between_them(self):
        opened = [{"target_set": "s", "target": f"o{i}", "order": i} for i in range(40)]
        names = lambda ts: {t["target"] for t in ts}
        halves = [names(h.pick({"open": opened, "solved": []}, 99, 0, lambda t: True, (k, 2))) for k in (0, 1)]
        self.assertEqual((halves[0] & halves[1], halves[0] | halves[1]), (set(), names(opened)))
        gone = min(halves[0])                                                    # solved by half 0's run
        later = {"open": [t for t in opened if t["target"] != gone], "solved": []}
        self.assertEqual(names(h.pick(later, 99, 0, lambda t: True, (1, 2))), halves[1])

    def test_a_replication_draws_fresh_solved_problems_and_leaves_the_slices_alone(self):
        targets = {"open": [{"target_set": "s", "target": f"o{i}", "order": i} for i in range(20)],
                   "solved": [{"target_set": "s", "target": f"d{i}", "rung": "amc12"} for i in range(40)]}
        names = lambda ts: [t["target"] for t in ts]
        first = h.pick(targets, 0, 10, lambda t: True)
        again = h.pick(targets, 0, 10, lambda t: True, seed="replication", used=set(names(first)))
        self.assertEqual(len(again), 10)
        self.assertFalse(set(names(first)) & set(names(again)))
        self.assertEqual(names(h.pick(targets, 99, 0, lambda t: True, (1, 2))),
                         names(h.pick(targets, 99, 0, lambda t: True, (1, 2), seed="replication")))

    def test_the_goal_is_the_theorem_itself(self):
        self.assertEqual(h.theorem_as_goal(TARGET), "theorem sb_goal (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by")

    def test_alone_judges_the_raw_answer_and_stops_at_the_first_accept(self):
        replies = iter([answer("  nlinarith\n"), answer("  positivity\n"), answer("  positivity\n")])
        judged = []
        judge = lambda t: (judged.append(t), {"verdict": "accept" if "positivity" in t else "reject"})[1]
        cand, k = h.alone(TARGET, lambda p: next(replies), judge, calls=4)
        self.assertEqual(k, 2)
        self.assertEqual(len(judged), 2)                     # no fixer, no loop: one judge per answer

    def test_alone_gives_up_after_its_budget(self):
        calls = []
        cand, k = h.alone(TARGET, lambda p: (calls.append(p), answer("  nlinarith\n"))[1],
                          lambda t: {"verdict": "reject"}, calls=3)
        self.assertEqual((cand, k, len(calls)), (None, None, 3))

    def test_tools_get_the_same_budget(self):
        seen = {}
        def fake(statement, prefix, **kw):
            seen.update(kw["budget"])
            return None
        with mock.patch.object(decompose, "decompose", side_effect=fake):
            h.with_tools(TARGET, None, None, lambda t: {"verdict": "reject"}, calls=3)
        self.assertEqual(seen["max"], 3)

    def test_both_arms_run_on_every_problem_in_a_seeded_order(self):
        t = {"target_set": "s", "target": "t1", "status": "solved", "rung": "aime"}
        call = lambda p: {"text": answer("  positivity\n"), "tokens": 10}
        with mock.patch.object(decompose, "decompose", return_value="  positivity\n"):
            rows, solves = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=2)
        self.assertEqual(sorted(r["arm"] for r in rows), ["alone", "tools"])
        self.assertEqual(solves, [])                         # a solved problem is measured, never re-published
        rows2, _ = h.run([t], lambda s, n: TARGET, call, None, lambda x: {"verdict": "accept"}, calls=2)
        self.assertEqual([r["arm"] for r in rows], [r["arm"] for r in rows2])

    def test_the_summary_counts_the_paired_disagreements(self):
        rows = [{"arm": "alone", "target": "a", "outcome": "failed", "calls": 4, "tokens": 40, "seconds": 9},
                {"arm": "tools", "target": "a", "outcome": "solved", "calls": 2, "tokens": 30, "seconds": 20},
                {"arm": "alone", "target": "b", "outcome": "solved", "calls": 1, "tokens": 10, "seconds": 5},
                {"arm": "tools", "target": "b", "outcome": "solved", "calls": 1, "tokens": 12, "seconds": 8}]
        s = h.summary(rows)
        self.assertEqual((s["only_tools"], s["only_alone"]), (["a"], []))
        self.assertEqual((s["alone"]["solved"], s["tools"]["solved"]), (1, 2))
        self.assertEqual(s["alone"]["calls_per_solve"], 5.0)   # every call the arm spent, over its solves
        self.assertEqual(s["tools"]["calls_per_solve"], 1.5)


if __name__ == "__main__":
    unittest.main()
