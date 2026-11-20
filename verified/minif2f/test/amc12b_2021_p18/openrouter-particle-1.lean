import Mathlib

open scoped Nat
open scoped Real

/--
Let $z$ be a complex number satisfying $12\lvert z\rvert^2 = 2 \lvert z+2 \rvert ^2+\lvert z^2+1\rvert ^2+31.$ What is the value of $z+\frac{6}{z}?$


$\textbf{(A) }-2\qquad\textbf{(B) }-1\qquad\textbf{(C) }\frac{1}{2}\qquad\textbf{(D) }1\qquad\textbf{(E) }4$ -/
theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by
  let x : ℝ := z.re
  let y : ℝ := z.im
  have hnormz : Complex.normSq z = x ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply]
    simp [x, y, pow_two] <;> ring
  have hnormz2 : Complex.normSq (z + 2) = (x + 2) ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply]
    simp [x, y, Complex.add_re, Complex.add_im, pow_two] <;> ring
  have hnormz21 : Complex.normSq (z ^ 2 + 1) =
      (x ^ 2 - y ^ 2 + 1) ^ 2 + (2 * x * y) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [x, y, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      pow_two] <;> ring
  have hpoly : 12 * (x ^ 2 + y ^ 2) =
      2 * ((x + 2) ^ 2 + y ^ 2) +
        ((x ^ 2 - y ^ 2 + 1) ^ 2 + (2 * x * y) ^ 2) + 31 := by
    simpa [hnormz, hnormz2, hnormz21] using h₀
  have hsq : (x ^ 2 + y ^ 2 - 6) ^ 2 + 4 * (x + 1) ^ 2 = 0 := by
    nlinarith [hpoly]
  have hA2 : (x ^ 2 + y ^ 2 - 6) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - 6), sq_nonneg (x + 1), hsq]
  have hB2 : (x + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - 6), sq_nonneg (x + 1), hsq]
  have hA : x ^ 2 + y ^ 2 - 6 = 0 := by
    have h := hA2
    rw [pow_two] at h
    exact mul_self_eq_zero.mp h
  have hB : x + 1 = 0 := by
    have h := hB2
    rw [pow_two] at h
    exact mul_self_eq_zero.mp h
  have hx : x = -1 := by linarith
  have hsum : x ^ 2 + y ^ 2 = 6 := by linarith
  have hy2 : y ^ 2 = 5 := by nlinarith [hsum, hx]
  have hz_eq : z = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [x, y]
    · simp [x, y]
  have hquad : z ^ 2 + 2 * z + 6 = 0 := by
    rw [hz_eq]
    apply Complex.ext
    · simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        pow_two, hx] <;> nlinarith [hy2]
    · simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        pow_two, hx] <;> ring
  have hz_ne : z ≠ 0 := by
    intro hz0
    have h0 : Complex.normSq z = 0 := by simp [hz0]
    rw [hnormz] at h0
    nlinarith [hsum]
  field_simp [hz_ne]
  linear_combination hquad
