import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 8: pow_pow. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L08pow_pow.lean, Apache-2.0. -/
theorem primer_power_08_pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  exact (pow_mul a m n).symm
