import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 2: zero_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L02zero_mul.lean, Apache-2.0. -/
theorem primer_multiplication_02_zero_mul (m : ℕ) : 0 * m = 0 := by
  ring
