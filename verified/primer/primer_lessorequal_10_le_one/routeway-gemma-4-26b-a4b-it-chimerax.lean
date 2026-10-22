import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 10: le_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L10le_one.lean, Apache-2.0. -/
theorem primer_lessorequal_10_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with
  | zero => left; rfl
  | succ n =>
    cases n with
    | zero => right; rfl
    | succ m =>
      have h_le_one : Nat.succ (Nat.succ m) ≤ 1 := hx
      linarith
