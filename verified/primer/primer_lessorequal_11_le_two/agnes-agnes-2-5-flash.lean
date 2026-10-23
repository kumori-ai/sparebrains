import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have h : x ≤ 2 := hx
  cases x with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inr (Or.inl rfl)
    | succ m =>
      cases m with
      | zero => exact Or.inr (Or.inr rfl)
      | succ k =>
        have : k + 4 ≤ 2 := by simpa using h
        omega
