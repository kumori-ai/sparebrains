import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 10: mul_right_eq_self. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L10mul_right_eq_self.lean, Apache-2.0. -/
theorem primer_advmultiplication_10_mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  have h₁ : a * b = a * 1 := by
    simpa [Nat.mul_one] using h
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero ha) h₁
