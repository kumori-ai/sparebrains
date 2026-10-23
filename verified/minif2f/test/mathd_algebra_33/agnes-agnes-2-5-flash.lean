import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h₃ : y = 2 * x / 5 := by
    field_simp [show (5 : ℝ) ≠ 0 by norm_num] at h₁ ⊢
    linarith
  have h₄ : z = 7 * x / 25 := by
    rw [h₃] at h₂
    field_simp [show (7 : ℝ) ≠ 0 by norm_num, show (5 : ℝ) ≠ 0 by norm_num] at h₂ ⊢
    ring_nf at h₂ ⊢
    linarith
  rw [h₄]
  field_simp [h₀, show (25 : ℝ) ≠ 0 by norm_num]
  <;> ring
  <;> norm_num
