import Mathlib

open scoped Nat
open scoped Real

/--
Positive real numbers $x \neq 1$ and $y \neq 1$ satisfy $\log_2{x} = \log_y{16}$ and $xy = 64$. What is $(\log_2{\tfrac{x}{y}})^2$?

$\textbf{(A) } \frac{25}{2} \qquad\textbf{(B) } 20 \qquad\textbf{(C) } \frac{45}{2} \qquad\textbf{(D) } 25 \qquad\textbf{(E) } 32$ -/
theorem amc12a_2019_p12 (x y : ℝ) (h₀ : x ≠ 1 ∧ y ≠ 1)
    (h₁ : Real.log x / Real.log 2 = Real.log 16 / Real.log y) (h₂ : x * y = 64) :
    (Real.log (x / y) / Real.log 2) ^ 2 = 20 := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx] at h₂
    norm_num at h₂
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy] at h₂
    norm_num at h₂
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
    rw [h16, Real.log_pow]
    push_cast
    ring
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    have h64 : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
    rw [h64, Real.log_pow]
    push_cast
    ring
  have hsum : Real.log x + Real.log y = 6 * Real.log 2 := by
    have h := congrArg Real.log h₂
    rw [Real.log_mul hx0 hy0, hlog64] at h
    exact h
  have hylog : Real.log y ≠ 0 := by
    intro hy
    rw [hy, div_zero] at h₁
    have hxlog : Real.log x = 0 := by
      have h := div_eq_zero_iff.mp h₁
      rcases h with h | h
      · exact h
      · exact absurd h hlog2
    rw [hxlog, hy] at hsum
    have h6 : (6 : ℝ) * Real.log 2 = 0 := by linarith
    have hlog2zero : Real.log 2 = 0 := by
      rcases mul_eq_zero.mp h6 with h | h
      · norm_num at h
      · exact h
    exact hlog2 hlog2zero
  have hprod : Real.log x * Real.log y = 4 * (Real.log 2) ^ 2 := by
    have h := h₁
    rw [hlog16, div_eq_div_iff hlog2 hylog] at h
    rw [h]
    ring
  have key : (Real.log x - Real.log y) ^ 2 = 20 * (Real.log 2) ^ 2 := by
    have h : (Real.log x - Real.log y) ^ 2
        = (Real.log x + Real.log y) ^ 2 - 4 * (Real.log x * Real.log y) := by ring
    rw [h, hsum, hprod]
    ring
  rw [Real.log_div hx0 hy0, div_pow, key]
  have hc2 : (Real.log 2) ^ 2 ≠ 0 := pow_ne_zero 2 hlog2
  field_simp
