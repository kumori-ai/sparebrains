import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 2: exact practice. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L02exact2.lean, Apache-2.0. -/
theorem primer_implication_02_exact2 (x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  rw [Nat.zero_add, Nat.zero_add] at h
  exact h
