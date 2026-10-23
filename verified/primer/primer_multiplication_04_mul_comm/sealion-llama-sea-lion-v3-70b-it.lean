import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 4: mul_comm. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L04mul_comm.lean, Apache-2.0. -/
theorem primer_multiplication_04_mul_comm (a b : ℕ) : a * b = b * a := by
  induction a with
  | zero => simp
  | succ a ih => simp [ih, Nat.mul_succ, Nat.succ_mul]
