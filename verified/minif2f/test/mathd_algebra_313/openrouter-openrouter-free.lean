import Mathlib

open scoped Nat
open scoped Real

/--
Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have hz : z ≠ 0 := by
    rw [h₂]
    norm_num [Complex.ext_iff, Complex.I_mul_I, Complex.I_mul_I]
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try simp_all [Complex.ext_iff, Complex.I_mul_I, Complex.I_mul_I]) <;>
    (try norm_num) <;>
    (try linarith)
  
  have h3 : i = v / z := by
    have h3 : v = i * z := h₀
    have h4 : z ≠ 0 := hz
    have h5 : i = v / z := by
      calc
        i = i * 1 := by ring
        _ = i * (z * z⁻¹) := by field_simp [h4]
        _ = (i * z) * z⁻¹ := by ring
        _ = v * z⁻¹ := by rw [h3]
        _ = v / z := by
          field_simp [h4]
          <;> ring
    exact h5
  
  have h4 : i = (1 + Complex.I) / (2 - Complex.I) := by
    rw [h3]
    rw [h₁, h₂]
    <;> norm_num
    <;> simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
    <;> norm_num
    <;> field_simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
    <;> ring_nf
    <;> norm_num
    <;> simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
    <;> norm_num
  
  have h5 : (1 + Complex.I) / (2 - Complex.I) = 1 / 5 + 3 / 5 * Complex.I := by
    have h₅ : (1 + Complex.I : ℂ) / (2 - Complex.I) = 1 / 5 + 3 / 5 * Complex.I := by
      -- Use the property of complex numbers to simplify the division
      field_simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq, Complex.I_mul_I]
      <;> norm_num <;>
      (try ring_nf) <;>
      (try norm_num) <;>
      (try simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq, Complex.I_mul_I]) <;>
      (try norm_num) <;>
      (try linarith)
      <;>
      simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq, Complex.I_mul_I]
      <;>
      norm_num
      <;>
      linarith
    rw [h₅]
    <;> norm_num
  
  rw [h4, h5]
  <;> norm_num
