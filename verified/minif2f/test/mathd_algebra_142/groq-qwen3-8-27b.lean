import Mathlib

open scoped Nat
open scoped Real

/--
A line $\ell$ passes through the points $B(7,-1)$ and $C(-1,7)$.  The equation of this line can be written in the form $y=mx+b$; compute $m+b$. -/
theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  have h₂ : m = -1 := by
    have h₂₁ : m * 7 + b - (m * -1 + b) = -1 - 7 := by
      rw [h₀, h₁]
    have h₂₂ : m * 7 + b - (m * -1 + b) = m * 8 := by ring
    have h₂₃ : m * 8 = -8 := by linarith
    have h₂₄ : m = -1 := by linarith
    exact h₂₄
  have h₃ : b = 6 := by
    have h₃₁ : m * -1 + b = 7 := h₁
    rw [h₂] at h₃₁
    linarith
  rw [h₂, h₃]
  norm_num
