import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 3: making life simple. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L03add_algo2.lean, Apache-2.0. -/
theorem primer_algorithm_03_add_algo2 (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  ring
