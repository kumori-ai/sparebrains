import Mathlib

open scoped Nat
open scoped Real

/--
Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
  have h_eq : i * (2 - Complex.I) = 1 + Complex.I := by
    calc
      i * (2 - Complex.I) = i * z := by rw [h₂]
      _ = v := by rw [← h₀]
      _ = 1 + Complex.I := h₁
  have h_target : (1 / 5 + 3 / 5 * Complex.I) * (2 - Complex.I) = 1 + Complex.I := by
    field_simp
    ring
    simp [Complex.I_sq]
    ring
  have h_den_ne_zero : (2 - Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  apply mul_right_cancel₀ h_den_ne_zero
  calc
    i * (2 - Complex.I) = 1 + Complex.I := h_eq
    _ = (1 / 5 + 3 / 5 * Complex.I) * (2 - Complex.I) := by rw [h_target]
