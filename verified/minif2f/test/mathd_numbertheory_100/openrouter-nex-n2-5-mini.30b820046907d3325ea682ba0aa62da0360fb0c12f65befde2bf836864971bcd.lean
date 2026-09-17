import Mathlib

open scoped Nat
open scoped Real

/-- Find $n$ if $\gcd(n,40) = 10$ and $\mathop{\text{lcm}}[n,40] = 280$. -/
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have h₃ : Nat.gcd n 40 * Nat.lcm n 40 = n * 40 := Nat.gcd_mul_lcm n 40
  rw [h₁, h₂] at h₃
  norm_num at h₃
  omega
