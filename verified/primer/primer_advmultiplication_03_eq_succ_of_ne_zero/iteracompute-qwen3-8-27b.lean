import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 3: eq_succ_of_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L03eq_succ_of_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_03_eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = Nat.succ n := by
  cases a with
  | zero =>
    exfalso
    exact ha rfl
  | succ n =>
    exact ⟨n, rfl⟩
