import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 8: mul_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L08mul_eq_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_08_mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · left
    exact ha
  · right
    by_contra hb
    exact (Nat.mul_ne_zero ha hb) h
