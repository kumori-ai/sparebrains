import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 6: add_left_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L06add_left_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_06_add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  intro h
  exact (Nat.add_eq_zero_iff.1 h).2
