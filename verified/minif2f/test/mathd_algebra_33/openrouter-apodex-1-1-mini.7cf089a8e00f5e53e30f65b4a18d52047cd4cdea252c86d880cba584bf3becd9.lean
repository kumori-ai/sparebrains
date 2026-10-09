import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h₃ : z = (7 / 10) * y := by
    calc
      z = 10 * z / 10 := by field_simp
      _ = 7 * y / 10 := by rw [h₂]
      _ = (7 / 10) * y := by ring
  have h₄ : y = (2 / 5) * x := by
    calc
      y = 5 * y / 5 := by field_simp
      _ = 2 * x / 5 := by rw [h₁]
      _ = (2 / 5) * x := by ring
  calc
    z / x = ((7 / 10) * y) / x := by rw [h₃]
    _ = (7 / 10) * (y / x) := by field_simp [h₀]
    _ = (7 / 10) * ((2 / 5) * x / x) := by rw [h₄]
    _ = (7 / 10) * (2 / 5) := by field_simp [h₀]
    _ = 7 / 25 := by norm_num
