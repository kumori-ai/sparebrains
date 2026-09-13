import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 2: making life easier. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L02add_algo1.lean, Apache-2.0. -/
theorem primer_algorithm_02_add_algo1 (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  omega
