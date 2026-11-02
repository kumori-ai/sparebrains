import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the first 5 terms of an arithmetic series is $70$.  The sum of the first 10 terms of this  arithmetic series is $210$.  What is the first term of the series? -/
theorem mathd_algebra_342 (a d : ℝ) (h₀ : ∑ k ∈ Finset.range 5, (a + k * d) = 70)
    (h₁ : ∑ k ∈ Finset.range 10, (a + k * d) = 210) : a = 42 / 5 := by
  have h5 : ∑ k ∈ Finset.range 5, (a + k * d) = 5*a + 10*d := by
    simp [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have h10 : ∑ k ∈ Finset.range 10, (a + k * d) = 10*a + 45*d := by
    simp [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have h5_eq : 5*a + 10*d = 70 := by
    linarith [h₀, h5]
  have h10_eq : 10*a + 45*d = 210 := by
    linarith [h₁, h10]
  linarith
