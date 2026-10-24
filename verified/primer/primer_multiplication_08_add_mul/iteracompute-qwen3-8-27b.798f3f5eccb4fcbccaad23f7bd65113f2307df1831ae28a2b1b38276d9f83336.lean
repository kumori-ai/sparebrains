import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 8: add_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L08add_mul.lean, Apache-2.0. -/
theorem primer_multiplication_08_add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  exact Nat.add_mul a b c
