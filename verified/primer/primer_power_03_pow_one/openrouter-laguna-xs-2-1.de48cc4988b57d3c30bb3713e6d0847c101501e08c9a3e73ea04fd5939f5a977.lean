import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 3: pow_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L03pow_one.lean, Apache-2.0. -/
theorem primer_power_03_pow_one (a : ℕ) : a ^ 1 = a := by
  exact pow_one a
