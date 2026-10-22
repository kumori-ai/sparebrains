import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 2: zero_pow_succ. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L02zero_pow_succ.lean, Apache-2.0. -/
theorem primer_power_02_zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (Nat.succ m) = 0 := by
  simp [Nat.pow_succ]
