import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 5: pow_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L05pow_two.lean, Apache-2.0. -/
theorem primer_power_05_pow_two (a : ℕ) : a ^ 2 = a * a := by
  exact pow_two a
