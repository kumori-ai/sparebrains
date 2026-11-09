import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exfalso
      apply h
      simp [hb]
    · exact hb
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_of_nonneg_left hb (Nat.zero_le a)
