import Mathlib

open scoped Nat
open scoped Real

/-- Find $n$ if $\gcd(n,40) = 10$ and $\mathop{\text{lcm}}[n,40] = 280$. -/
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have hprod : n * 40 = 70 * 40 := by
    calc
      n * 40 = Nat.gcd n 40 * Nat.lcm n 40 := (Nat.gcd_mul_lcm n 40).symm
      _ = 10 * 280 := by rw [h₁, h₂]
      _ = 2800 := by norm_num
      _ = 70 * 40 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 40) hprod
