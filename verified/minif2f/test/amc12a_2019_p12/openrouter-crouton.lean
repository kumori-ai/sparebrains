import Mathlib

open scoped Nat
open scoped Real

/--
Positive real numbers $x \neq 1$ and $y \neq 1$ satisfy $\log_2{x} = \log_y{16}$ and $xy = 64$. What is $(\log_2{\tfrac{x}{y}})^2$?

$\textbf{(A) } \frac{25}{2} \qquad\textbf{(B) } 20 \qquad\textbf{(C) } \frac{45}{2} \qquad\textbf{(D) } 25 \qquad\textbf{(E) } 32$ -/
theorem amc12a_2019_p12 (x y : ℝ) (h₀ : x ≠ 1 ∧ y ≠ 1)
    (h₁ : Real.log x / Real.log 2 = Real.log 16 / Real.log y) (h₂ : x * y = 64) :
    (Real.log (x / y) / Real.log 2) ^ 2 = 20 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h₂
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at h₂
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≠ 0 := ne_of_gt hLpos
  have h64pos : 0 < Real.log 64 := Real.log_pos (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    have h : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h, Real.log_pow]
    push_cast
    ring
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    have h : (64 : ℝ) = 2 ^ 6 := by norm_num
    rw [h, Real.log_pow]
    push_cast
    ring
  have hsum_log : Real.log x + Real.log y = Real.log 64 := by
    rw [← Real.log_mul hx0 hy0, h₂]
  have hB : Real.log y ≠ 0 := by
    intro hBy
    have h1z : Real.log x / Real.log 2 = 0 := by
      have h := h₁
      rw [hBy, div_zero] at h
      exact h
    have hAx : Real.log x = 0 := by
      rcases div_eq_zero_iff.mp h1z with h | h
      · exact h
      · exact (hL h).elim
    rw [hAx, hBy] at hsum_log
    have h64z : Real.log 64 = 0 := by simpa using hsum_log.symm
    exact (ne_of_gt h64pos) h64z
  have hAB : Real.log x * Real.log y = Real.log 16 * Real.log 2 :=
    (div_eq_div_iff hL hB).mp h₁
  have hAB2 : Real.log x * Real.log y = 4 * (Real.log 2) ^ 2 := by
    rw [h16] at hAB
    ring_nf at hAB ⊢
    exact hAB
  have hSum : Real.log x + Real.log y = 6 * Real.log 2 := by
    rw [h64] at hsum_log
    exact hsum_log
  have hlogdiv : Real.log (x / y) = Real.log x - Real.log y :=
    Real.log_div hx0 hy0
  rw [hlogdiv]
  have hsq : (Real.log x - Real.log y) ^ 2 = 20 * (Real.log 2) ^ 2 := by
    have h : (Real.log x - Real.log y) ^ 2
        = (Real.log x + Real.log y) ^ 2 - 4 * (Real.log x * Real.log y) := by ring
    rw [h, hSum, hAB2]
    ring
  rw [div_pow, hsq, mul_div_cancel_right₀ 20 (pow_ne_zero 2 hL)]
