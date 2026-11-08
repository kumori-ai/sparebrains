import Mathlib

open scoped Nat
open scoped Real

/--
Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have hz : z ≠ 0 := by
    rw [h₂]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have key : (1 / 5 + 3 / 5 * Complex.I) * z = v := by
    rw [h₂, h₁]
    linear_combination (-3 / 5 : ℂ) * Complex.I_mul_I
  have hmul : i * z = (1 / 5 + 3 / 5 * Complex.I) * z := by
    rw [← h₀]
    exact key.symm
  exact mul_right_cancel₀ hz hmul
