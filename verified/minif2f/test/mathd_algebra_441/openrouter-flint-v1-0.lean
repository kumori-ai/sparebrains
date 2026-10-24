import Mathlib

open scoped Nat
open scoped Real

/-- Assuming $x\ne0$, simplify $\frac{12}{x \cdot x} \cdot \frac{x^4}{14x}\cdot \frac{35}{3x}$. -/
theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  have h14 : (14 * x) ≠ 0 := by
    exact mul_ne_zero (by norm_num) h₀
  have h3 : (3 * x) ≠ 0 := by
    exact mul_ne_zero (by norm_num) h₀
  have hx2 : (x * x) ≠ 0 := by
    exact mul_ne_zero h₀ h₀
  field_simp [h₀, h14, h3, hx2]
  ring
