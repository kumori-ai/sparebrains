import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have hsum1 : (↑(∑ k ∈ Finset.range 8, (2 * k + 1)) : ℤ) = 64 := by
    push_cast
    norm_num
  have hsum2 : (↑(∑ k ∈ Finset.range 5, (a + 2 * k)) : ℤ) = 5 * (a : ℤ) + 20 := by
    push_cast
    simp [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hsum1, hsum2] at h₁
  have ha_int : (a : ℤ) = 8 := by linarith
  exact_mod_cast ha_int
