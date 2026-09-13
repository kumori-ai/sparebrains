import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h_sum : a + b + c = 5 := by
    have h_add : (3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) = (-3 : ℝ) + 9 + 19 := by
      rw [h₀, h₁, h₂]
    have h_add' : (3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) = 5 * (a + b + c) := by
      ring
    rw [h_add'] at h_add
    linarith
  have ha : a = -4 := by
    have h_diff : (3 * a + b + c) - (a + b + c) = (-3 : ℝ) - 5 := by
      rw [h₀, h_sum]
    have h_diff' : (3 * a + b + c) - (a + b + c) = 2 * a := by
      ring
    rw [h_diff'] at h_diff
    linarith
  have hb : b = 2 := by
    have h_diff : (a + 3 * b + c) - (a + b + c) = 9 - 5 := by
      rw [h₁, h_sum]
    have h_diff' : (a + 3 * b + c) - (a + b + c) = 2 * b := by
      ring
    rw [h_diff'] at h_diff
    linarith
  have hc : c = 7 := by
    have h_diff : (a + b + 3 * c) - (a + b + c) = 19 - 5 := by
      rw [h₂, h_sum]
    have h_diff' : (a + b + 3 * c) - (a + b + c) = 2 * c := by
      ring
    rw [h_diff'] at h_diff
    linarith
  rw [ha, hb, hc]
  norm_num
