import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 9: zero_ne_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L09zero_ne_succ.lean, Apache-2.0. -/
theorem primer_implication_09_zero_ne_succ : (0 : ℕ) ≠ 1 := by
  intro h
  injection h
