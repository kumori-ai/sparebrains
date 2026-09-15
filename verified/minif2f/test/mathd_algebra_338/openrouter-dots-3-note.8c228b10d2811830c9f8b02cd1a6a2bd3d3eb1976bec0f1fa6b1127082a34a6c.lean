import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have hsum : a + b + c = 5 := by
    have h : 5 * (a + b + c) = 25 := by
      calc
        5 * (a + b + c) = (3*a + b + c) + (a + 3*b + c) + (a + b + 3*c) := by ring
        _ = -3 + 9 + 19 := by rw [h₀, h₁, h₂]
        _ = 25 := by norm_num
    linarith
  have ha : a = -4 := by
    nlinarith
  have hb : b = 2 := by
    nlinarith
  have hc : c = 7 := by
    nlinarith
  rw [ha, hb, hc]
  norm_num
