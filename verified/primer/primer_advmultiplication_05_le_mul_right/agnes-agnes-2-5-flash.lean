import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have h₁ : a ≠ 0 := by
    intro ha
    rw [ha] at h
    norm_num at h
  have h₂ : b ≠ 0 := by
    intro hb
    rw [hb] at h
    norm_num at h
  have hb_ge_one : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr h₂
  have h_mul : a * 1 ≤ a * b := Nat.mul_le_mul_left a hb_ge_one
  have h_one : a * 1 = a := Nat.mul_one a
  rw [h_one] at h_mul
  exact h_mul
