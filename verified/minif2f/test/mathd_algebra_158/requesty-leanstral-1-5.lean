import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have hsum1 : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) = (64 : ℤ) := by norm_num
  rw [hsum1] at h₁
  have hsum : ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (5 : ℤ) * (a : ℤ) + 20 := by
    simp [Finset.sum_range_succ, Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hsum] at h₁
  have ha : (a : ℤ) = 8 := by linarith
  exact_mod_cast ha
