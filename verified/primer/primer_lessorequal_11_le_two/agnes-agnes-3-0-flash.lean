import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases x with
  | zero =>
    exact Or.inl rfl
  | succ x' =>
    cases x' with
    | zero =>
      exact Or.inr (Or.inl rfl)
    | succ x'' =>
      cases x'' with
      | zero =>
        exact Or.inr (Or.inr rfl)
      | succ x''' =>
        have h : 2 + 1 + 1 ≤ 2 := by
          simpa using hx
        contradiction
