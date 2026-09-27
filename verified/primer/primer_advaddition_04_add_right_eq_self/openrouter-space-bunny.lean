import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 4: add_right_eq_self. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L04add_right_eq_self.lean, Apache-2.0. -/
theorem primer_advaddition_04_add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  omega
