import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 4: one_pow. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L04one_pow.lean, Apache-2.0. -/
theorem primer_power_04_one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  simp
