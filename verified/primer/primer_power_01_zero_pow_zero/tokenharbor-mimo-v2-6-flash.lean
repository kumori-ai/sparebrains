import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 1: zero_pow_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L01zero_pow_zero.lean, Apache-2.0. -/
theorem primer_power_01_zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  exact pow_zero _
