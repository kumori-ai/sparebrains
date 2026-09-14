import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 4: mul_comm. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L04mul_comm.lean, Apache-2.0. -/
theorem primer_multiplication_04_mul_comm (a b : ℕ) : a * b = b * a := by
  induction a with
  | zero =>
    show 0 * b = b * 0
    rw [Nat.mul_zero, Nat.zero_mul]
  | succ a ih =>
    show (a + 1) * b = b * (a + 1)
    rw [Nat.add_mul, Nat.mul_succ, ih, Nat.one_mul]
