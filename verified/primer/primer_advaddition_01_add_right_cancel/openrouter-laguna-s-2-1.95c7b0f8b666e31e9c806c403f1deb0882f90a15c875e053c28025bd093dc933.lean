import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 1: add_right_cancel. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L01add_right_cancel.lean, Apache-2.0. -/
theorem primer_advaddition_01_add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  intro h
  induction n with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero] at h
    exact h
  | succ n ih =>
    rw [Nat.add_succ, Nat.add_succ] at h
    exact ih (Nat.succ_inj.mp h)
