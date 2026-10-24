import Mathlib

/-- Natural Number Game (Lean 4), Tutorial world, level 8: 2+2=4. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Tutorial/L08twoaddtwo.lean, Apache-2.0. -/
theorem primer_tutorial_08_twoaddtwo : (2 : ℕ) + 2 = 4 := by
  norm_num
