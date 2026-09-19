import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 3: The apply tactic. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L03apply.lean, Apache-2.0. -/
theorem primer_implication_03_apply (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  exact h2 h1
