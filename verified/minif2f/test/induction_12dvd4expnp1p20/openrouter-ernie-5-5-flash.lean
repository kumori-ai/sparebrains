import Mathlib

open scoped Nat
open scoped Real

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  induction n with
  | zero => exact ⟨2, by norm_num⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨4 * m - 5, ?_⟩
    rw [pow_succ]
    omega
