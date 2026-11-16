import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  have hsq : (n : ℤ) ^ 2 = 4096 := by
    nlinarith [h₁]
  have hx_nonneg : (0 : ℤ) ≤ n := by
    exact_mod_cast Nat.zero_le n
  have hfactor : ((n : ℤ) - 64) * ((n : ℤ) + 64) = 0 := by
    nlinarith [hsq]
  have hpos : (n : ℤ) + 64 ≠ 0 := by
    have : 0 < (n : ℤ) + 64 := by
      nlinarith [hx_nonneg]
    exact ne_of_gt this
  have hx : (n : ℤ) - 64 = 0 := by
    exact (mul_eq_zero.mp hfactor).resolve_right hpos
  have hn : n = 64 := by
    have : (n : ℤ) = 64 := by
      omega
    exact_mod_cast this
  subst n
  norm_num
