import Mathlib

open scoped Nat
open scoped Real

/--
The product of two positive whole numbers is 2005. If neither number is 1, what is the sum of the two numbers? -/
theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by
  have hsmall : m ≤ 44 ∨ n ≤ 44 := by
    by_contra h
    push Not at h
    have hm45 : 45 ≤ m := by omega
    have hn45 : 45 ≤ n := by omega
    have hprod : 45 * 45 ≤ m * n :=
      Nat.mul_le_mul hm45 hn45
    omega
  rcases hsmall with hm | hn
  · interval_cases m <;> omega
  · interval_cases n <;> omega
