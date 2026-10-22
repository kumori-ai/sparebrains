import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 5: add_right_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L05add_right_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_05_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  intro h
  cases a with
  | zero => rfl
  | succ a' =>
      rw [Nat.add_zero] at h
      have h' : a' + 1 = 0 := by
        simpa [Nat.add_assoc] using h
      have h'' : a' = 0 := by
        omega
      have h''' : 0 + 1 = 0 := by
        simpa [h''] using h
      simp at h'''
