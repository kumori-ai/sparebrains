import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  have hx_nonneg : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hexp : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = 3 * (↑n : ℤ) ^ 2 + 8 := by ring
  rw [hexp] at h₁
  have hx2 : (n : ℤ) ^ 2 = 4096 := by linarith
  have hfactor : ((n : ℤ) - 64) * ((n : ℤ) + 64) = 0 := by
    have h : ((n : ℤ) - 64) * ((n : ℤ) + 64) = (n : ℤ) ^ 2 - 4096 := by ring
    rw [h, hx2]
    norm_num
  have hn : (n : ℤ) = 64 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  rw [hn]
  norm_num
