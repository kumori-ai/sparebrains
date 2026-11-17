import Mathlib

open scoped Nat
open scoped Real

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h4 : 4 ∣ 4 ^ (n + 1) := by
        exact ⟨4 ^ n, by rw [pow_succ]; ring⟩
      have hdiff : 12 ∣ 3 * 4 ^ (n + 1) := by
        obtain ⟨k, hk⟩ := h4
        exact ⟨k, by rw [hk]; ring⟩
      have hsum : 4 ^ (n + 1 + 1) + 20 = (4 ^ (n + 1) + 20) + 3 * 4 ^ (n + 1) := by
        rw [show 4 ^ (n + 1 + 1) = 4 ^ (n + 1) * 4 by rw [pow_succ]]
        ring
      change 12 ∣ 4 ^ (n + 1 + 1) + 20
      rw [hsum]
      exact dvd_add ih hdiff
