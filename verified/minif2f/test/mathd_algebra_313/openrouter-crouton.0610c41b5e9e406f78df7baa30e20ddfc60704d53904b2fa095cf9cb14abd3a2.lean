import Mathlib

open scoped Nat
open scoped Real

/--
Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have hz : (2 - Complex.I) ≠ 0 := by
    intro h
    have hre : (2 - Complex.I).re = (0 : ℂ).re := congrArg Complex.re h
    simp at hre
  have hiz : i * (2 - Complex.I) = 1 + Complex.I := by
    have h : i * (2 - Complex.I) = i * z := by rw [h₂]
    rw [h, ← h₀, h₁]
  have hcalc : (1 / 5 + 3 / 5 * Complex.I) * (2 - Complex.I) = 1 + Complex.I := by
    calc (1 / 5 + 3 / 5 * Complex.I) * (2 - Complex.I)
        = 2 / 5 - 1 / 5 * Complex.I + 6 / 5 * Complex.I
          - 3 / 5 * (Complex.I * Complex.I) := by ring
      _ = 1 + Complex.I := by rw [Complex.I_mul_I]; ring
  have h : i * (2 - Complex.I)
      = (1 / 5 + 3 / 5 * Complex.I) * (2 - Complex.I) := by rw [hiz, hcalc]
  exact mul_right_cancel₀ hz h
