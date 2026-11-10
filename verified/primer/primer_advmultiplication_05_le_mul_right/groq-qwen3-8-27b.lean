import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≠ 0 := by
    intro hb0
    rw [hb0, Nat.mul_zero] at h
    exact h rfl
  have hb' : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb)
  calc
    a = a * 1 := by ring
    _ ≤ a * b := Nat.mul_le_mul_left a hb'
