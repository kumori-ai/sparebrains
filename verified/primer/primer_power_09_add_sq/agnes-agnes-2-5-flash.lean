import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 9: add_sq. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L09add_sq.lean, Apache-2.0. -/
theorem primer_power_09_add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  calc
  (a + b) ^ 2 = (a + b) * (a + b) := by simp [pow_two]
  _ = a * a + b * a + a * b + b * b := by ring
  _ = a ^ 2 + b ^ 2 + 2 * a * b := by ring
