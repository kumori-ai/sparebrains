import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the first 5 terms of an arithmetic series is $70$.  The sum of the first 10 terms of this  arithmetic series is $210$.  What is the first term of the series? -/
theorem mathd_algebra_342 (a d : ℝ) (h₀ : ∑ k ∈ Finset.range 5, (a + k * d) = 70)
    (h₁ : ∑ k ∈ Finset.range 10, (a + k * d) = 210) : a = 42 / 5 := by
  have key : ∀ n : ℕ, ∑ k ∈ Finset.range n, (a + (k : ℝ) * d)
      = (n : ℝ) * a + (n : ℝ) * ((n : ℝ) - 1) / 2 * d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have e5 := key 5
  have e10 := key 10
  rw [h₀] at e5
  rw [h₁] at e10
  norm_num at e5 e10
  linarith
