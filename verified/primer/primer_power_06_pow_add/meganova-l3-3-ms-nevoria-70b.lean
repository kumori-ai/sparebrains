import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 6: pow_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L06pow_add.lean, Apache-2.0. -/
theorem primer_power_06_pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, pow_succ, ih, mul_assoc, pow_succ]
