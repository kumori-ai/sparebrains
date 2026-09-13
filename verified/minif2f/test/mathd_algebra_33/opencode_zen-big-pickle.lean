import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have hy : y = (2 / 5) * x := by
    linarith
  have hz : z = (7 / 10) * y := by
    linarith
  calc
    z / x = ((7 / 10) * y) / x := by rw [hz]
    _ = ((7 / 10) * ((2 / 5) * x)) / x := by rw [hy]
    _ = 7 / 25 := by
      field_simp [h₀]
      ring
