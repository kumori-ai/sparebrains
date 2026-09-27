import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  by_cases hb : b = 0
  · simp [hb] at h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    simp only [Nat.succ_eq_add_one, Nat.mul_add]
    omega
