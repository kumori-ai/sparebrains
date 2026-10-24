import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 3: eq_succ_of_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L03eq_succ_of_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_03_eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = Nat.succ n := by
  use a.pred
  rw [Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero ha)]
