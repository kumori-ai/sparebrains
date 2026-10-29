import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases x with
  | zero =>
    left
    rfl
  | succ x =>
    cases x with
    | zero =>
      right
      left
      rfl
    | succ x =>
      cases x with
      | zero =>
        right
        right
        rfl
      | succ x =>
        have h1 : x.succ.succ ≤ 1 := Nat.le_of_succ_le_succ hx
        have h2 : x.succ ≤ 0 := Nat.le_of_succ_le_succ h1
        exfalso
        exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le (Nat.succ_pos x) h2)
