import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 8: pow_pow. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L08pow_pow.lean, Apache-2.0. -/
theorem primer_power_08_pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (a ^ m) ^ (n + 1) = (a ^ m) ^ n * (a ^ m) := by
        simp only [Nat.pow_succ]
      _ = a ^ (m * n) * (a ^ m) := by
        rw [ih]
      _ = a ^ (m * n + m) := by
        simp only [Nat.pow_add]
      _ = a ^ (m * (n + 1)) := by
        simp only [Nat.mul_succ]
