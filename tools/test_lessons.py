"""tools/lessons.py: the lessons station. Nearest solved theorems by statement, their kernel-accepted proofs as the
lesson; never the problem's own proof, never a proof of the same statement. No Lean, no network."""
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


if __name__ == "__main__":
    unittest.main()
