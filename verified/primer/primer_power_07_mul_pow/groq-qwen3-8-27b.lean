import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 7: mul_pow. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L07mul_pow.lean, Apache-2.0. -/
theorem primer_power_07_mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  exact mul_pow a b n
