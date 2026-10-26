import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have : b ≠ 0 := by
    intro hb
    rw [hb, MulZeroClass.mul_zero] at h
    exact h rfl
  have : b ≥ 1 := by
    apply Nat.succ_le_of_lt
    exact Nat.pos_of_ne_zero this
  apply Nat.le_mul_of_pos_right
  exact this
