import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
  have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := Nat.mul_le_mul (le_refl a) hb1
