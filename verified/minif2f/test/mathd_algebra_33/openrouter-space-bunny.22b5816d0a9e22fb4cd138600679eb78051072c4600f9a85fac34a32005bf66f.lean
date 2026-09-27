import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h₃ : 25 * z = 7 * x := by
    linarith
  calc
    z / x = (25 * z) / (25 * x) := by
      field_simp [h₀]
    _ = (7 * x) / (25 * x) := by
      rw [h₃]
    _ = 7 / 25 := by
      field_simp [h₀]
