import Mathlib

open scoped Nat
open scoped Real

/-- Assuming $x\ne0$, simplify $\frac{12}{x \cdot x} \cdot \frac{x^4}{14x}\cdot \frac{35}{3x}$. -/
theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  have h1 : x * x ≠ 0 := mul_ne_zero h₀ h₀
  have h2 : (14 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) h₀
  have h3 : (3 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) h₀
  field_simp [h1, h2, h3]
  ring
