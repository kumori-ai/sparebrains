import Mathlib

open scoped Nat
open scoped Real

/--
Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have h : i * (2 - Complex.I) = 1 + Complex.I := by
    calc i * (2 - Complex.I) = i * z := by rw [h₂]
      _ = v := h₀.symm
      _ = 1 + Complex.I := h₁
  have hprod : (2 - Complex.I) * (2 + Complex.I) = 5 := by
    have h1 : (2 - Complex.I) * (2 + Complex.I) = 4 - Complex.I * Complex.I := by ring
    rw [h1, Complex.I_mul_I]
    norm_num
  have hprod2 : (1 + Complex.I) * (2 + Complex.I) = 1 + 3 * Complex.I := by
    have h1 : (1 + Complex.I) * (2 + Complex.I) = 2 + 3 * Complex.I + Complex.I * Complex.I := by ring
    rw [h1, Complex.I_mul_I]
    ring
  have h5 : i * 5 = 1 + 3 * Complex.I := by
    calc i * 5 = i * ((2 - Complex.I) * (2 + Complex.I)) := by rw [hprod]
      _ = (i * (2 - Complex.I)) * (2 + Complex.I) := by ring
      _ = (1 + Complex.I) * (2 + Complex.I) := by rw [h]
      _ = 1 + 3 * Complex.I := hprod2
  linear_combination (1 / 5 : ℂ) * h5
