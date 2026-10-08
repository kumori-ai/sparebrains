"""tools/subgoals.py: APOLLO's loop with Lean and the model faked. The output shapes are Lean 4.33.1's,
copied from real runs on 2026-10-08 (a positioned error, an `extract_goal` statement after a trace
marker, the never-executed linter on a `first | ...` line).

    python3 tools/test_subgoals.py
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import subgoals as sg

PREFIX = "import Mathlib\n\ntheorem demo (p : ℕ) (hp : p.Prime) (hd : p ∣ 12) (n : ℕ) (h : 3 ≤ n) :\n    (p = 2 ∨ p = 3) ∧ 2 < n := by"
TOP = PREFIX.count("\n") + 1


class Messages(unittest.TestCase):
    def test_positioned_messages_and_their_continuations(self):
        out = ("proof.lean:6:12: error(lean.unknownIdentifier): Unknown constant `Nat.foo`\n"
               "proof.lean:3:62: error: unsolved goals\np : ℕ\n⊢ p ≤ 12\n"
               "proof.lean:5:97: warning: aesop: failed to prove the goal after exhaustive search.\n")
        ms = sg.messages(out)
        self.assertEqual([(l, c, k) for l, c, k, _ in ms], [(6, 12, "error"), (3, 62, "error"), (5, 97, "warning")])
        self.assertIn("⊢ p ≤ 12", ms[1][3])
        self.assertEqual(len(sg.errors(out)), 2)


class Sorrify(unittest.TestCase):
    def test_a_failed_have_keeps_its_claim(self):
        text = PREFIX + "\n  have h2 : 2 < n := by\n    exact Nat.foo h\n  exact ⟨sorry, h2⟩"
        line = TOP + 1                                   # the `have` line; the error is at its `by`
        out = sg.sorrify(text, [(line, text.split("\n")[line - 1].index(" by") + 1, "unsolved goals")], TOP)
        self.assertIn("have h2 : 2 < n := by\n    sorry\n  exact", out)

    def test_an_inline_calc_step_keeps_its_claim(self):
        step = "      _ = v / z := by field_simp; ring"
        text = PREFIX + "\n  calc\n    n = n := rfl\n" + step + "\n      _ = n := by rfl"
        out = sg.sorrify(text, [(TOP + 3, step.index(" by") + 1, "unsolved goals")], TOP)   # Lean points at `by`
        self.assertIn("      _ = v / z := by\n        sorry\n      _ = n := by rfl", out)

    def test_a_failed_step_takes_the_rest_of_its_sequence(self):
        text = PREFIX + "\n  rw [Nat.foo] at h\n  simp at h\n  exact h"
        out = sg.sorrify(text, [(TOP + 1, 2, "Unknown constant")], TOP)
        self.assertEqual(out.split("\n")[TOP:], ["  sorry"])

    def test_a_failed_bullet_leaves_its_siblings(self):
        text = PREFIX + "\n  constructor\n  · exact Nat.foo hp\n  · omega"
        out = sg.sorrify(text, [(TOP + 2, 10, "Unknown constant")], TOP)
        self.assertEqual(out.split("\n")[TOP:], ["  constructor", "  · sorry", "  · omega"])

    def test_goals_left_at_the_end_append_a_hole(self):
        text = PREFIX + "\n  constructor"
        out = sg.sorrify(text, [(TOP, 30, "unsolved goals")], TOP)
        self.assertEqual(out.split("\n")[TOP:], ["  constructor", "  sorry"])

    def test_several_cases_left_at_the_end_get_one_hole_for_all(self):
        text = PREFIX + "\n  interval_cases n <;> simp"
        out = sg.sorrify(text, [(TOP, 30, "unsolved goals\ncase «1»\n⊢ x\n\ncase «2»\n⊢ y")], TOP)
        self.assertEqual(out.split("\n")[TOP:], ["  interval_cases n <;> simp", "  all_goals sorry"])
        self.assertEqual(sg._with_tactics(out, {TOP + 1: [sg.AUTO]}).split("\n")[-1], "  all_goals (" + sg.AUTO + ")")

    def test_a_step_after_the_goal_closed_is_dropped(self):
        text = PREFIX + "\n  omega\n  simp"
        out = sg.sorrify(text, [(TOP + 2, 2, "no goals to be proved")], TOP)
        self.assertEqual(out.split("\n")[TOP:], ["  omega"])
        text = PREFIX + "\n  rw [foo]\n  · sorry\n  · sorry\n  · ring_nf\n  · ring_nf"   # Lean 4.33's wording
        out = sg.sorrify(text, [(TOP + 3, 2, "No goals to be solved")], TOP)
        self.assertEqual(out.split("\n")[TOP:], ["  rw [foo]", "  · sorry"])

    def test_nothing_to_change_is_none(self):
        self.assertIsNone(sg.sorrify(PREFIX + "\n  sorry", [(TOP + 1, 2, "x")], TOP))


class Holes(unittest.TestCase):
    def test_inline_holes_move_to_their_own_line(self):
        text = PREFIX + "\n  have a : p ≤ 12 := by sorry\n  have b : 2 < n := sorry\n  exact ⟨by omega, b⟩"
        norm = sg.normalize_holes(text, TOP)
        self.assertEqual(norm.split("\n")[TOP:TOP + 4],
                         ["  have a : p ≤ 12 := by", "    sorry", "  have b : 2 < n := by", "    sorry"])
        self.assertEqual(len(sg.holes(norm, TOP)), 2)

    def test_a_sorry_inside_a_term_is_not_a_hole_we_can_fill(self):
        self.assertIsNone(sg.holes(PREFIX + "\n  exact ⟨sorry, by omega⟩", TOP))

    def test_kept_steps(self):
        self.assertEqual(sg.kept_steps(PREFIX + "\n  sorry", TOP), 0)
        self.assertEqual(sg.kept_steps(PREFIX + "\n  constructor\n  · sorry\n  · omega", TOP), 2)


class Executed(unittest.TestCase):
    def test_the_last_alternative_not_called_never_executed_is_the_one_that_ran(self):
        line = "  · " + sg.AUTO
        cols = {t: line.index(t) for t in sg.AUTO_TACTICS}
        after = sg.AUTO_TACTICS[sg.AUTO_TACTICS.index("nlinarith") + 1:]
        msgs = [(9, cols[t], "warning", sg.NEVER_RUN) for t in after]
        self.assertEqual(sg._executed(line, 9, msgs), "nlinarith")
        self.assertIsNone(sg._executed(line, 9, []))      # no linter output: unknown, keep the combinator


class Names(unittest.TestCase):
    def test_invented_library_names_get_real_ones_and_local_names_do_not(self):
        said = "x.lean:4:8: error(lean.unknownIdentifier): Unknown constant `Nat.coprime_pow_eq_pow_iff`\nUnknown identifier `h7`"
        lines = sg.real_names(said, lambda n: ["Nat.pow_left_injective", n])
        self.assertIn("`Nat.coprime_pow_eq_pow_iff` does not exist: real names close to it: `Nat.pow_left_injective`", lines)
        self.assertNotIn("h7", lines)
        self.assertEqual(sg.real_names(said, None), "")


def fake_lean(script):
    """run_lean / judge_text fakes that answer in order from `script` and record what they were shown."""
    seen = []

    def run_lean(text):
        seen.append(text)
        return script.pop(0), 1.0

    def judge_text(text):
        seen.append(text)
        return script.pop(0)
    return run_lean, judge_text, seen


class Repair(unittest.TestCase):
    PROOF = "\n  constructor\n  · exact Nat.Prime.eq_two_or_three_of_dvd_twelve hp hd\n  · exact Nat.foo h"
    FIRST = ("x.lean:6:10: error(lean.unknownIdentifier): Unknown constant `Nat.Prime.eq_two_or_three_of_dvd_twelve`\n"
             "x.lean:7:10: error(lean.unknownIdentifier): Unknown constant `Nat.foo`\n")
    GOAL = "theorem demo.extracted_1_1 (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ 12) : p = 2 ∨ p = 3 := sorry"

    def run_repair(self, replies, lemma_verdicts, final="accept"):
        script = [
            {"verdict": "wellformed", "output": "", "reason": "sorry"},                   # after the holes
            "proof.lean:6:4: error: Tactic `first` failed\n",                              # AUTO: hole 1 fails, hole 2 closes
            "sb_hole 1\n" + self.GOAL + "\nsb_auto 2\n",                                    # the probe
        ] + [{"verdict": v, "output": "proof.lean:4:8: error: nope" if v != "accept" else "", "reason": v}
             for v in lemma_verdicts] + [{"verdict": final, "output": "", "reason": final}]
        run_lean, judge_text, seen = fake_lean(script)
        asked, lemmas = [], []

        def ask(prompt):
            asked.append(prompt)
            return replies.pop(0)
        log = sg.repair(PREFIX + self.PROOF, PREFIX, self.FIRST, ask=ask, run_lean=run_lean, judge_text=judge_text,
                        on_lemma=lambda st, t: lemmas.append((st, t["verdict"])))
        return log, asked, lemmas, seen

    def test_closed_by_lean_then_a_lemma_from_the_model_then_the_kernel(self):
        good = "```lean\ntheorem sb_goal (p : ℕ) : p = 2 ∨ p = 3 := by\n  interval_cases p <;> omega\n```"
        log, asked, lemmas, seen = self.run_repair(["```lean\ntheorem sb_goal := by\n  exact bad\n```", good],
                                                    ["reject", "accept"])
        self.assertEqual(log["final"], "accept")
        self.assertEqual((log["closed_by_lean"], log["lemmas_proved"], log["asked"]), (1, 1, 2))
        self.assertIn("Lean said:\n```\nproof.lean:4:8: error: nope", asked[1])       # the retry carries the error
        self.assertIn("theorem sb_goal (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ 12) : p = 2 ∨ p = 3 := by", asked[0])
        self.assertEqual([v for _, v in lemmas], ["reject", "accept"])
        # the lemma is judged on OUR statement, never the model's (it dropped hp and hd above)
        self.assertIn("(hd : p ∣ 12) : p = 2 ∨ p = 3 := by\n  interval_cases p <;> omega", seen[-2])
        self.assertIn("  · interval_cases p <;> omega\n  · " + sg.AUTO, log["accepted"])

    def test_an_unproved_step_stops_with_a_sketch_and_no_accept(self):
        log, asked, _, _ = self.run_repair(["no lean here", "still none"], [])
        self.assertNotIn("accepted", log)
        self.assertEqual(log["stopped"], "1 of 1 open steps unproved")
        self.assertIn("· sorry", log["sketch"])
        self.assertEqual(len(asked), 2)

    def test_no_positioned_error_means_nothing_to_do(self):
        run_lean, judge_text, _ = fake_lean([])
        log = sg.repair(PREFIX + "\n  omega", PREFIX, "timeout after 300s", ask=None, run_lean=run_lean, judge_text=judge_text)
        self.assertEqual(log["stopped"], "Lean reported no failing step")

    def test_a_proof_thrown_away_whole_is_not_worth_a_lemma(self):
        run_lean, judge_text, _ = fake_lean([{"verdict": "wellformed", "output": "", "reason": ""}])
        log = sg.repair(PREFIX + "\n  exact Nat.foo", PREFIX, "x.lean:5:2: error: Unknown constant `Nat.foo`",
                        ask=None, run_lean=run_lean, judge_text=judge_text)
        self.assertEqual(log["stopped"], "no step of the proof survived")


class Queue(unittest.TestCase):
    SKETCH = PREFIX + "\n  constructor\n  · sorry\n  · omega"
    GOAL = "theorem demo.extracted_1_1 (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ 12) : p = 2 ∨ p = 3 := sorry"

    def test_the_next_lane_gets_the_step_the_first_could_not_prove(self):
        script = ["proof.lean:6:4: error: Tactic `first` failed\n",          # automation: the hole stays open
                  "sb_hole 1\n" + self.GOAL + "\n",
                  {"verdict": "reject", "output": "proof.lean:4:8: error: nope", "reason": "x"},
                  {"verdict": "reject", "output": "proof.lean:4:8: error: nope", "reason": "x"},
                  {"verdict": "accept", "output": "", "reason": "ok"},          # lane 2's first answer
                  {"verdict": "accept", "output": "", "reason": "ok"}]          # the spliced whole
        run_lean, judge_text, seen = fake_lean(script)
        weak = lambda p: "```lean\ntheorem sb_goal := by\n  exact nope\n```"
        strong = lambda p: "```lean\ntheorem sb_goal := by\n  interval_cases p <;> omega\n```"
        who = []
        log = sg.prove_sketch(self.SKETCH, PREFIX, asks=[weak, strong], run_lean=run_lean, judge_text=judge_text,
                              on_lemma=lambda st, t: who.append((t["by"], t["verdict"])))
        self.assertEqual(log["final"], "accept")
        self.assertEqual(who, [(0, "reject"), (0, "reject"), (1, "accept")])
        self.assertEqual(log["provers"], [1])
        self.assertIn("  · interval_cases p <;> omega\n  · omega", log["accepted"])


if __name__ == "__main__":
    unittest.main(verbosity=1)
