import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the first 5 terms of an arithmetic series is $70$.  The sum of the first 10 terms of this  arithmetic series is $210$.  What is the first term of the series? -/
theorem mathd_algebra_342 (a d : ℝ) (h₀ : ∑ k ∈ Finset.range 5, (a + k * d) = 70)
    (h₁ : ∑ k ∈ Finset.range 10, (a + k * d) = 210) : a = 42 / 5 := by
  have h₂ : 5 * a + 10 * d = 70 := by
    simp [Finset.sum_range_succ] at h₀
    ring_nf at h₀ ⊢
    exact h₀
  have h₃ : 10 * a + 45 * d = 210 := by
    simp [Finset.sum_range_succ] at h₁
    ring_nf at h₁ ⊢
    exact h₁
  linarith
