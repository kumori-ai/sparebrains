import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 8: ≠. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L08ne.lean, Apache-2.0. -/
theorem primer_implication_08_ne (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  exact h2 h1
