import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 2: mul_left_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L02mul_left_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_02_mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  intro hb
  apply h
  rw [hb, mul_zero]
