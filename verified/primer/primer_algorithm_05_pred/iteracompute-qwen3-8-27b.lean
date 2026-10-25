import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 5: pred. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L05pred.lean, Apache-2.0. -/
theorem primer_algorithm_05_pred (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  exact Nat.succ_injective h
