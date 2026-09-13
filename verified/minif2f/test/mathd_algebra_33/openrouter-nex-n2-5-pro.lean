import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h₃ : y = 2 / 5 * x := by
    linarith
  have h₄ : z = 7 / 10 * y := by
    linarith
  have h₅ : z = 7 / 25 * x := by
    rw [h₄, h₃]
    ring
  rw [h₅]
  field_simp [h₀]
