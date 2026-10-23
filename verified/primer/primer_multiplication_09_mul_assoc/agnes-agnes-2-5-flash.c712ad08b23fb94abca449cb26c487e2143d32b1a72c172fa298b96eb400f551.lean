import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 9: mul_assoc. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L09mul_assoc.lean, Apache-2.0. -/
theorem primer_multiplication_09_mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    simp_all [Nat.mul_succ, Nat.add_assoc]
    <;> ring_nf at *
    <;> simp_all
