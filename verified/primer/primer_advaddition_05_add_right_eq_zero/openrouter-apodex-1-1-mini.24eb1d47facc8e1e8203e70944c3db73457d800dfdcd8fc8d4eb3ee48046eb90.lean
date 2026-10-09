import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 5: add_right_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L05add_right_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_05_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  intro h
  exact (Nat.add_eq_zero_iff.mp h).1
