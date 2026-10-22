import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 6: mul_right_eq_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L06mul_right_eq_one.lean, Apache-2.0. -/
theorem primer_advmultiplication_06_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp at h
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp at h
  have hy_one : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy
  have hle : x ≤ x * y := by
    calc
      x = x * 1 := by simp
      _ ≤ x * y := Nat.mul_le_mul_left x hy_one
  rw [h] at hle
  have hx_one : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
  exact le_antisymm hle hx_one
