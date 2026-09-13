import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 6: intro. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L06intro.lean, Apache-2.0. -/
theorem primer_implication_06_intro (x : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h
