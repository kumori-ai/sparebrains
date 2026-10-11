import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have h₂ : (∑ k ∈ Finset.range 8, (2 * k + 1) : ℕ) = 64 := by rfl
  have h₃ : (∑ k ∈ Finset.range 5, (a + 2 * k) : ℕ) = 5 * a + 20 := by
    simp [Finset.sum_range_succ]
    <;> ring
  rw [h₂, h₃] at h₁
  have h₄ : (a : ℤ) = 8 := by omega
  exact_mod_cast h₄
