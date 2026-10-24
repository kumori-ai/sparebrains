import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 9: succ_le_succ. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L09succ_le_succ.lean, Apache-2.0. -/
theorem primer_lessorequal_09_succ_le_succ (x y : ℕ) (hx : Nat.succ x ≤ Nat.succ y) : x ≤ y := by
  cases' x with x
  cases' y with y
  all_goals simp_all [Nat.le_of_lt_succ, Nat.succ_le_succ]
  all_goals
    exact Nat.le_of_lt_succ (Nat.lt_of_succ_le hx)
