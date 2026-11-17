import Mathlib

open scoped Nat
open scoped Real

/--
The product of two consecutive positive even integers is 288. What is the greater of the two integers? -/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have hm : m = n + 2 := by omega
  have hmn : (n + 2) * n = 288 := by
    simpa [hm] using h₃
  have hZ : ((n : ℤ) + 2) * (n : ℤ) = 288 := by
    have hcast : (((n + 2) * n : ℕ) : ℤ) = (288 : ℤ) := by
      exact_mod_cast hmn
    norm_num [Nat.cast_add, Nat.cast_mul] at hcast
    exact hcast
  have hfac : ((n : ℤ) - 16) * ((n : ℤ) + 18) = 0 := by
    nlinarith
  have hnZ : (n : ℤ) = 16 := by
    have hnnonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
    rcases mul_eq_zero.mp hfac with h | h
    · omega
    · omega
  have hn : n = 16 := by
    exact_mod_cast hnZ
  omega
