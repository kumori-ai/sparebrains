import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 6: mul_right_eq_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L06mul_right_eq_one.lean, Apache-2.0. -/
theorem primer_advmultiplication_06_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have hpos_y : 1 ≤ y := by
    by_contra hy
    push_neg at hy
    have : y = 0 := by omega
    rw [this] at h
    simp at h
  have hpos_x : 1 ≤ x := by
    by_contra hx
    push_neg at hx
    have : x = 0 := by omega
    rw [this] at h
    simp at h
  have hx1 : x ≤ 1 := by
    calc
      x = x * 1 := by rw [Nat.mul_one]
      _ ≤ x * y := Nat.mul_le_mul_left x hpos_y
      _ = 1 := h
  omega
