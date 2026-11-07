import Mathlib

open scoped Nat
open scoped Real

/--
Let $z$ be a complex number satisfying $12\lvert z\rvert^2 = 2 \lvert z+2 \rvert ^2+\lvert z^2+1\rvert ^2+31.$ What is the value of $z+\frac{6}{z}?$


$\textbf{(A) }-2\qquad\textbf{(B) }-1\qquad\textbf{(C) }\frac{1}{2}\qquad\textbf{(D) }1\qquad\textbf{(E) }4$ -/
theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by
  have e1 : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have e2 : Complex.normSq (z + 2) = (z.re + 2) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have e3 : Complex.normSq (z ^ 2 + 1)
      = (z.re ^ 2 - z.im ^ 2 + 1) ^ 2 + (2 * z.re * z.im) ^ 2 := by
    simp [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [e1, e2, e3] at h₀
  have key : (z.re ^ 2 + z.im ^ 2 - 6) ^ 2 + 4 * (z.re + 1) ^ 2 = 0 := by
    linear_combination -h₀
  have h_nonneg1 : 0 ≤ (z.re ^ 2 + z.im ^ 2 - 6) ^ 2 := sq_nonneg _
  have h_nonneg2 : 0 ≤ 4 * (z.re + 1) ^ 2 := by positivity
  have h_both := (add_eq_zero_iff_of_nonneg h_nonneg1 h_nonneg2).mp key
  have h_r : z.re ^ 2 + z.im ^ 2 - 6 = 0 := sq_eq_zero_iff.mp h_both.1
  have h_x2 : (z.re + 1) ^ 2 = 0 := by
    have h := h_both.2
    have h' : (z.re + 1) ^ 2 = 0 := by
      have : 4 * (z.re + 1) ^ 2 = 0 := h
      simpa using this
    exact h'
  have h_x : z.re + 1 = 0 := sq_eq_zero_iff.mp h_x2
  have hre : z.re = -1 := by linarith
  have hr : z.re ^ 2 + z.im ^ 2 = 6 := by linarith
  have hy2 : z.im ^ 2 = 5 := by
    rw [hre] at hr
    nlinarith
  have hz_ne : z ≠ 0 := by
    intro hz
    have hre0 : z.re = 0 := by rw [hz]; simp
    linarith
  have hz_eq : z = -1 + (z.im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z, hre]
    simp
  have hquad : z ^ 2 + 2 * z + 6 = 0 := by
    rw [hz_eq]
    have hyC : (z.im : ℂ) ^ 2 = 5 := by exact_mod_cast hy2
    linear_combination (z.im : ℂ) ^ 2 * Complex.I_mul_I - hyC
  have hfinal : z + 6 / z + 2 = 0 := by
    have h3 : (z ^ 2 + 2 * z + 6) / z = z + 6 / z + 2 := by
      field_simp [hz_ne]
      ring
    rw [← h3, hquad]
    simp
  exact eq_neg_of_add_eq_zero_left hfinal
