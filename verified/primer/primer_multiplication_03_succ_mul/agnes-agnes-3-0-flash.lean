import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 3: succ_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L03succ_mul.lean, Apache-2.0. -/
theorem primer_multiplication_03_succ_mul (a b : ℕ) : Nat.succ a * b = a * b + b := by
  simp [Nat.succ_mul]
