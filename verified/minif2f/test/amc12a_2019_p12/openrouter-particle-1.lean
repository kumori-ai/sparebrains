import Mathlib

open scoped Nat
open scoped Real

/--
Positive real numbers $x \neq 1$ and $y \neq 1$ satisfy $\log_2{x} = \log_y{16}$ and $xy = 64$. What is $(\log_2{\tfrac{x}{y}})^2$?

$\textbf{(A) } \frac{25}{2} \qquad\textbf{(B) } 20 \qquad\textbf{(C) } \frac{45}{2} \qquad\textbf{(D) } 25 \qquad\textbf{(E) } 32$ -/
theorem amc12a_2019_p12 (x y : ℝ) (h₀ : x ≠ 1 ∧ y ≠ 1)
    (h₁ : Real.log x / Real.log 2 = Real.log 16 / Real.log y) (h₂ : x * y = 64) :
    (Real.log (x / y) / Real.log 2) ^ 2 = 20 := by
  have hcpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Real.log 2 ≠ 0 := ne_of_gt hcpos
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at h₂
    norm_num at h₂
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at h₂
    norm_num at h₂
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hsum : Real.log x + Real.log y = 6 * Real.log 2 := by
    have h := Real.log_mul hx0 hy0
    rw [h₂] at h
    rw [← h, hlog64]
  have hLy : Real.log y ≠ 0 := by
    intro hLy0
    have hLx0 : Real.log x = 0 := by
      have h := h₁
      rw [hLy0, div_zero] at h
      exact (div_eq_zero_iff.mp h).resolve_right hc
    have h := hsum
    rw [hLx0, hLy0] at h
    nlinarith [hcpos]
  have hprod : Real.log x * Real.log y = 4 * (Real.log 2) ^ 2 := by
    have h := h₁
    rw [hlog16] at h
    field_simp [hc, hLy] at h
    nlinarith
  have hlogdiv : Real.log (x / y) = Real.log x - Real.log y :=
    Real.log_div hx0 hy0
  have hc2 : (Real.log 2) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [hlogdiv, div_pow]
  field_simp [hc2]
  have hsq : (Real.log x + Real.log y) ^ 2 = (6 * Real.log 2) ^ 2 := by rw [hsum]
  have hdiff : (Real.log x - Real.log y) ^ 2 =
      (Real.log x + Real.log y) ^ 2 - 4 * (Real.log x * Real.log y) := by ring
  rw [hdiff, hsq, hprod]
  ring
