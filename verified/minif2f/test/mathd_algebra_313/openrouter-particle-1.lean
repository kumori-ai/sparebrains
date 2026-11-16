import Mathlib

open scoped Nat
open scoped Real

/--
Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have h : i * (2 - Complex.I) = 1 + Complex.I := by
    rw [← h₂]
    exact h₀.symm.trans h₁
  have hre : 2 * i.re + i.im = 1 := by
    have h' := congrArg Complex.re h
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re] at h'
    linarith
  have him : 2 * i.im - i.re = 1 := by
    have h' := congrArg Complex.im h
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_im] at h'
    linarith
  have hre' : i.re = 1 / 5 := by linarith
  have him' : i.im = 3 / 5 := by linarith
  apply Complex.ext
  · rw [hre']
    norm_num
  · rw [him']
    norm_num
