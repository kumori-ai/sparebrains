import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 1: The exact tactic. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L01exact.lean, Apache-2.0. -/
theorem primer_implication_01_exact (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1
