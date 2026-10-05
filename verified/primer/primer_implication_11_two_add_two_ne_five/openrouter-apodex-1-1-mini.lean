import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 11: 2 + 2 ≠ 5. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L11two_add_two_ne_five.lean, Apache-2.0. -/
theorem primer_implication_11_two_add_two_ne_five : Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) ≠ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
  decide
