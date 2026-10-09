import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 7: An algorithm for equality. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L07succ_ne_succ.lean, Apache-2.0. -/
theorem primer_algorithm_07_succ_ne_succ (m n : ℕ) (h : m ≠ n) : Nat.succ m ≠ Nat.succ n := by
  intro h'
  exact h (Nat.succ_injective h')
