import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 7: intro practice. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L07intro2.lean, Apache-2.0. -/
theorem primer_implication_07_intro2 (x y : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  have h1 : x + 1 - 1 = y + 1 - 1
  · rw [h]
  have h2 : x = y
  · linarith [h1]
  exact h2
