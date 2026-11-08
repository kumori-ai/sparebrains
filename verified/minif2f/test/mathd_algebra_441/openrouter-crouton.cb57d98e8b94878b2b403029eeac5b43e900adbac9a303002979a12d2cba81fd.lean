import Mathlib

open scoped Nat
open scoped Real

/-- Assuming $x\ne0$, simplify $\frac{12}{x \cdot x} \cdot \frac{x^4}{14x}\cdot \frac{35}{3x}$. -/
theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 h₀
  have hden_eq : (x * x) * (14 * x) * (3 * x) = 42 * x ^ 4 := by ring
  have hnum_eq : 12 * x ^ 4 * 35 = 42 * x ^ 4 * 10 := by ring
  have hne : (42 : ℝ) * x ^ 4 ≠ 0 := mul_ne_zero (by norm_num) hx4
  rw [div_mul_div_comm, div_mul_div_comm, hnum_eq, hden_eq]
  simp [hne]
