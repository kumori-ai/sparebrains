import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the first 5 terms of an arithmetic series is $70$.  The sum of the first 10 terms of this  arithmetic series is $210$.  What is the first term of the series? -/
theorem mathd_algebra_342 (a d : ℝ) (h₀ : ∑ k ∈ Finset.range 5, (a + k * d) = 70)
    (h₁ : ∑ k ∈ Finset.range 10, (a + k * d) = 210) : a = 42 / 5 := by
  have h₂ : ∑ k ∈ Finset.range 5, (a + k * d) = 5 * a + d * (0 + 1 + 2 + 3 + 4) := by
    simp [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero]
    ring
  have h₃ : ∑ k ∈ Finset.range 10, (a + k * d) = 10 * a + d * (0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) := by
    simp [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero]
    ring
  have h₄ : 5 * a + d * 10 = 70 := by
    simp only [show (0 + 1 + 2 + 3 + 4 : ℝ) = 10 by ring] at h₂
    linarith
  have h₅ : 10 * a + d * 45 = 210 := by
    simp only [show (0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 : ℝ) = 45 by ring] at h₃
    linarith
  have h₆ : a = 42 / 5 := by
    have h₇ : d = (70 - 5 * a) / 10 := by
      have h₈ : 5 * a + d * 10 = 70 := h₄
      field_simp
      linarith
    rw [h₇] at h₅
    field_simp at h₅
    ring_nf at h₅
    linarith
  exact h₆
