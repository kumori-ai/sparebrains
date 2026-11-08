import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 1: add_right_cancel. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L01add_right_cancel.lean, Apache-2.0. -/
theorem primer_advaddition_01_add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  intro h
  exact Nat.add_right_cancel h
