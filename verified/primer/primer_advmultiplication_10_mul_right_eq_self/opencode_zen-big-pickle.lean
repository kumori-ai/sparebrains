import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 10: mul_right_eq_self. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L10mul_right_eq_self.lean, Apache-2.0. -/
theorem primer_advmultiplication_10_mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  have ha' : 0 < a := Nat.pos_of_ne_zero ha
  exact Nat.mul_left_cancel ha' (by simpa [mul_one] using h)
