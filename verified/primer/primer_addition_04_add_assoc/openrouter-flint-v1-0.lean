import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 4: add_assoc. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L04add_assoc.lean, Apache-2.0. -/
theorem primer_addition_04_add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  exact Nat.add_assoc a b c
