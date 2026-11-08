import Mathlib

open scoped Nat
open scoped Real

/--
Let $z$ be a complex number satisfying $12\lvert z\rvert^2 = 2 \lvert z+2 \rvert ^2+\lvert z^2+1\rvert ^2+31.$ What is the value of $z+\frac{6}{z}?$


$\textbf{(A) }-2\qquad\textbf{(B) }-1\qquad\textbf{(C) }\frac{1}{2}\qquad\textbf{(D) }1\qquad\textbf{(E) }4$ -/
theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by
  have h2 : (z.re ^ 2 + z.im ^ 2 - 6) ^ 2 + 4 * (z.re + 1) ^ 2 = 0 := by
    have h := h₀
    simp [Complex.normSq_apply, pow_two] at h
    linear_combination -h
  have hsq := (add_eq_zero_iff_of_nonneg (sq_nonneg (z.re ^ 2 + z.im ^ 2 - 6))
    (by positivity : (0 : ℝ) ≤ 4 * (z.re + 1) ^ 2)).mp h2
  have hr : z.re ^ 2 + z.im ^ 2 = 6 := by
    have h1 : z.re ^ 2 + z.im ^ 2 - 6 = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq.1
    linarith
  have hx : z.re = -1 := by
    have h1 : z.re + 1 = 0 := by
      have h2' : (z.re + 1) ^ 2 = 0 := by linarith [hsq.2]
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2'
    linarith
  have hy : z.im ^ 2 = 5 := by
    have hx2 : z.re ^ 2 = 1 := by rw [hx]; norm_num
    linarith [hr, hx2]
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [hz0] at hr
    simp at hr
  have hquad : z ^ 2 + 2 * z + 6 = 0 := by
    apply Complex.ext
    · simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [hr, hx, hy]
    · simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [hr, hx, hy]
  field_simp [hz_ne]
  linear_combination hquad
