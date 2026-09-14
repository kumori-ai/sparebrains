import Mathlib

open scoped Nat
open scoped Real

/--
A line $\ell$ passes through the points $B(7,-1)$ and $C(-1,7)$.  The equation of this line can be written in the form $y=mx+b$; compute $m+b$. -/
theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  have h₂ : m * 7 - m * -1 = -8 := by
    linarith [h₀, h₁]
  have h₃ : m = -1 := by
    calc
      m = m * 8 / 8 := by field_simp [show (8 : ℝ) ≠ 0 by norm_num]
      _ = (m * 7 - m * -1) / 8 := by ring
      _ = (-8) / 8 := by rw [h₂]
      _ = -1 := by norm_num
  have h₄ : b = 6 := by
    linarith [h₁, h₃]
  rw [h₃, h₄]
  norm_num
