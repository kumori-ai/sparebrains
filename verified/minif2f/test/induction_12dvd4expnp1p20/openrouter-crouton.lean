import Mathlib

open scoped Nat
open scoped Real

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  have h : 4 ^ (n + 1) ≡ 4 [MOD 12] := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [pow_succ]
      exact (Nat.ModEq.mul_right 4 ih).trans (by decide)
  have h2 : 4 ^ (n + 1) + 20 ≡ 0 [MOD 12] :=
    (Nat.ModEq.add_right 20 h).trans (by decide)
  exact Nat.modEq_zero_iff_dvd.mp h2
