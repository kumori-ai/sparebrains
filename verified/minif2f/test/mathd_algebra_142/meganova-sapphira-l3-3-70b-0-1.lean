import Mathlib

open scoped Nat
open scoped Real

/--
A line $\ell$ passes through the points $B(7,-1)$ and $C(-1,7)$.  The equation of this line can be written in the form $y=mx+b$; compute $m+b$. -/
theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  have h₂ : m * 7 + b - (m * -1 + b) = -1 - 7 := by linarith
  have h₃ : m * 8 = -8 := by linarith
  have h₄ : m = -1 := by linarith
  have h₅ : -1 * -1 + b = 7 := by linarith
  have h₆ : b = 6 := by linarith
  have h₇ : m + b = -1 + 6 := by linarith
  have h₈ : m + b = 5 := by linarith
  exact h₈
