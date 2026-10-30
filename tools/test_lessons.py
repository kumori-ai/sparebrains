"""tools/lessons.py: the lessons station. Nearest solved theorems by statement, their kernel-accepted proofs as the
lesson; never the problem's own proof, never a proof of the same statement. No Lean, no network."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import lessons

T = ("import Mathlib\n\ntheorem {name} (x y : ℝ) (h₀ : 0 < x) (h₁ : 0 < y) : 0 < x * y := by\n")
U = ("import Mathlib\n\ntheorem {name} (n : ℕ) (h : n % 4 = 3) : n % 2 = 1 := by\n")


def corpus(tmp):
    targets, verified = Path(tmp) / "targets" / "s", Path(tmp) / "verified" / "s"
    for name, tpl, proof in (("mul_pos_a", T, "  positivity\n"), ("mul_pos_b", T, "  exact mul_pos h₀ h₁\n"),
                             ("mod_a", U, "  omega\n")):
        targets.mkdir(parents=True, exist_ok=True)
        (targets / f"{name}.lean").write_text(tpl.format(name=name) + "  sorry\n")
        (verified / name).mkdir(parents=True, exist_ok=True)
        (verified / name / "lane.lean").write_text(tpl.format(name=name) + proof)
    (verified / "mul_pos_a" / "other.lean").write_text(T.format(name="mul_pos_a") + "  nlinarith [h₀, h₁]\n")
    return Path(tmp) / "targets", Path(tmp) / "verified"


class Lessons(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.targets, self.verified = corpus(self.tmp.name)
        self.ix = lessons.index(self.targets, self.verified)

    def tearDown(self):
        self.tmp.cleanup()

    def test_the_index_keeps_one_shortest_proof_per_solved_target(self):
        self.assertEqual(sorted(e["key"] for e in self.ix), ["s/mod_a", "s/mul_pos_a", "s/mul_pos_b"])
        self.assertEqual(next(e for e in self.ix if e["key"] == "s/mul_pos_a")["proof"], "  positivity\n")

    def test_the_key_guard_alone_drops_the_problem_itself(self):
        fresh = "import Mathlib\n\ntheorem mul_pos_a (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : 0 < p * q * q := by\n"
        got = lessons.nearest(self.ix, fresh, k=3, exclude="s/mul_pos_a")   # a different theorem, the same key
        self.assertNotIn("s/mul_pos_a", [e["key"] for e in got])
        self.assertIn("s/mul_pos_b", [e["key"] for e in got])

    def test_the_declaration_guard_alone_drops_the_same_theorem_under_any_name(self):
        got = lessons.nearest(self.ix, T.format(name="mul_pos_a"), k=3, exclude=None)   # no key given at all
        self.assertTrue(all("mul_pos" not in e["key"] for e in got))     # both mul_pos targets are this theorem

    def test_a_fresh_statement_gets_its_closest_neighbours(self):
        fresh = "import Mathlib\n\ntheorem q (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b * b := by\n"
        got = lessons.nearest(self.ix, fresh, k=2, exclude="s/q")
        self.assertEqual({e["key"] for e in got}, {"s/mul_pos_a", "s/mul_pos_b"})

    def test_the_block_shows_statements_and_proofs_and_names_the_count(self):
        fresh = "import Mathlib\n\ntheorem q (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by\n"
        block = lessons.block(self.ix, fresh, k=1, exclude="s/q")
        self.assertIn("## Lessons: 1 solved theorem", block)
        self.assertIn("positivity", block)
        self.assertNotIn("sorry", block)

    def test_the_same_theorem_under_another_name_is_not_a_lesson(self):
        renamed = T.format(name="mul_pos_z")                 # the solved mul_pos_a, new name, extra spaces
        got = lessons.nearest(self.ix, renamed.replace("(x y : ℝ)", "(x y  : ℝ)"), k=3, exclude="s/mul_pos_z")
        self.assertTrue(all("mul_pos" not in e["key"] for e in got))

    def test_no_neighbour_means_no_block(self):
        self.assertEqual(lessons.block([], "theorem z : True := by\n", k=3, exclude="s/z"), "")


V = ("import Mathlib\n\ntheorem {name} (x y : ℝ) (h₀ : 0 < x) (h₁ : 0 < y) : x % 2 = 1 := by\n")   # mul_pos's hypotheses, mod_a's conclusion


class ByConclusion(unittest.TestCase):
    """The goal-shape variant (kumori #574): nearest by what must be proved, not by the whole statement."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.targets, self.verified = corpus(self.tmp.name)
        self.ix = lessons.index(self.targets, self.verified)

    def tearDown(self):
        self.tmp.cleanup()

    def test_the_conclusion_is_what_follows_the_last_top_level_colon(self):
        self.assertEqual(lessons.conclusion(T.format(name="t")), "0 < x * y")
        self.assertEqual(lessons.conclusion("theorem t (f : ℕ → ℕ) (h : ∀ n, f n = n) : f 2 = 2 := by\n"), "f 2 = 2")

    def test_the_statement_tokens_are_the_pilots(self):                  # Codex f2, 2026-10-29: the control stays the control
        self.assertEqual(lessons.tokens("theorem t (a b : ℕ) : a.gcd b = 1 ∧ a < b := by\n"), ["a", "b", "ℕ", "a.gcd", "b", "∧", "a", "b"])

    def test_the_shape_keeps_names_and_operators_and_drops_variables(self):
        self.assertEqual(lessons.ctokens("theorem t (a b : ℕ) (h : 0 < a) : a.gcd b = Nat.lcm a b := by\n"),
                         ["gcd", "=", "lcm"])
        self.assertEqual(lessons.ctokens("theorem t (x : ℝ) : IsLeast {y | √y ≤ x ^ 2} 0 := by\n"),
                         ["IsLeast", "√", "≤", "^"])

    def test_by_conclusion_picks_the_proof_of_the_same_shape_over_the_same_hypotheses(self):
        got_s = lessons.nearest(self.ix, V.format(name="v"), k=1, exclude="s/v")
        got_c = lessons.nearest(self.ix, V.format(name="v"), k=1, exclude="s/v", by="conclusion")
        self.assertIn(got_s[0]["key"], ("s/mul_pos_a", "s/mul_pos_b"))      # the statement shares x, y, h₀, h₁
        self.assertEqual(got_c[0]["key"], "s/mod_a")                         # the conclusion shares % 2 = 1

    def test_stored_goals_are_shown_and_retrieved_by(self):
        goal = "theorem sb_goal (n : ℕ) (hn : 3 ≤ n) : n % 2 = 1 := by"
        block = lessons.block(self.ix, V.format(name="v"), k=1, exclude="s/v", by="conclusion", goals=[goal])
        self.assertIn("## Where the loop stopped: 1 one-step goal", block)
        self.assertIn(goal, block)
        self.assertIn("omega", block)                                        # mod_a's proof, nearest to the goal
        self.assertLess(block.index("## Where the loop stopped"), block.index("## Lessons"))

    def test_goals_for_reads_the_queue_and_skips_restated_or_unreadable_goals(self):
        q = Path(self.tmp.name) / "goal-queue.json"
        q.write_text(json.dumps([
            {"target_set": "s", "target": "v", "goal": "theorem sb_goal : 1 = 1 := by", "file_ok": True, "restates": False},
            {"target_set": "s", "target": "v", "goal": "theorem sb_goal : 2 = 2 := by", "file_ok": True, "restates": True},
            {"target_set": "s", "target": "v", "goal": "theorem sb_goal : 3 = 3 := by", "file_ok": False, "restates": False},
            {"target_set": "s", "target": "w", "goal": "theorem sb_goal : 4 = 4 := by", "file_ok": True, "restates": False}]))
        self.assertEqual(lessons.goals_for("s/v", q), ["theorem sb_goal : 1 = 1 := by"])
        self.assertEqual(lessons.goals_for("s/none", q), [])


if __name__ == "__main__":
    unittest.main()
