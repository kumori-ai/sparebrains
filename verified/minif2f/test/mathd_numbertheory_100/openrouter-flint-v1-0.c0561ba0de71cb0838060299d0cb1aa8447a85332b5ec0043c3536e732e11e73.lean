import Mathlib

open scoped Nat
open scoped Real

/-- Find $n$ if $\gcd(n,40) = 10$ and $\mathop{\text{lcm}}[n,40] = 280$. -/
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have hEq : n * 40 = Nat.gcd n 40 * Nat.lcm n 40 := by
    exact (Nat.gcd_mul_lcm n 40).symm
  rw [h₁, h₂] at hEq
  norm_num at hEq
  have hn : (n : ℤ) * 40 = 2800 := by exact_mod_cast hEq
  have hn' : (n : ℤ) = 70 := by nlinarith
  exact_mod_cast hn'
