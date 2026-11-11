import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≠ 0 := by
    intro hb
    apply h
    rw [hb, mul_zero]
  have hbpos : 0 < b := Nat.pos_iff_ne_zero.mpr hb
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hbpos
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := Nat.mul_le_mul_left a hb1
