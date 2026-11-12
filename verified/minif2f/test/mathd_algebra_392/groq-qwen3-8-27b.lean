import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  have h₂ : (3 : ℤ) * (↑n : ℤ) ^ 2 + 8 = 12296 := by
    ring_nf at h₁
    linarith
  have h₃ : (↑n : ℤ) ^ 2 = 4096 := by
    linarith
  have h₄ : (↑n : ℤ) = 64 := by
    have h₄₁ : (↑n : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le n
    nlinarith
  have h₅ : n = 64 := by
    exact_mod_cast h₄
  subst h₅
  norm_num
