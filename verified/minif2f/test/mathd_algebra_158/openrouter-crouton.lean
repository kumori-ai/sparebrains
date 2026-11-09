import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have hs1 : ∑ k ∈ Finset.range 8, (2 * k + 1) = 64 := by
    norm_num [Finset.sum_range_succ]
  have hs2 : ∑ k ∈ Finset.range 5, (a + 2 * k) = 5 * a + 20 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hs1, hs2] at h₁
  push_cast at h₁
  have ha : (a : ℤ) = 8 := by linarith
  exact_mod_cast ha
