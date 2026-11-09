import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  have hn2 : 2 ≤ n := by
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h₁
  have h1' : ((n : ℤ) - 2) ^ 2 + (n : ℤ) ^ 2 + ((n : ℤ) + 2) ^ 2 = (12296 : ℤ) := by
    push_cast [Nat.cast_sub hn2] at h₁
    exact h₁
  have hsq : (n : ℤ) ^ 2 = 4096 := by
    have h : ((n : ℤ) - 2) ^ 2 + (n : ℤ) ^ 2 + ((n : ℤ) + 2) ^ 2 = 3 * (n : ℤ) ^ 2 + 8 := by ring
    linarith
  have h64 : (n : ℤ) = 64 := by
    have h : (n : ℤ) ^ 2 = (64 : ℤ) ^ 2 := by
      rw [hsq]
      norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
    · exact h1
    · exfalso
      have hnn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      linarith
  have hn64 : n = 64 := by exact_mod_cast h64
  subst hn64
  norm_num
