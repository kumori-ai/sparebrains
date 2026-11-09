import Mathlib

open scoped Nat
open scoped Real

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3)
    (h₁ : 0 < r) : r ^ 3 + 1 / r ^ 3 = 5778 := by
  set x := r ^ ((1 : ℝ) / 3) with hx_def
  have hx_pos : 0 < x := Real.rpow_pos_of_pos h₁ _
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx3 : x ^ 3 = r := by
    rw [← Real.rpow_natCast x 3, hx_def, ← Real.rpow_mul (le_of_lt h₁),
      show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have e2 : x ^ 2 + 1 / x ^ 2 = 7 := by
    have h : (x + 1 / x) ^ 2 = x ^ 2 + 1 / x ^ 2 + 2 := by field_simp; ring
    rw [h₀] at h
    norm_num at h
    simp only [one_div] at h ⊢
    linarith
  have e3 : x ^ 3 + 1 / x ^ 3 = 18 := by
    have h : (x + 1 / x) ^ 3 = (x ^ 3 + 1 / x ^ 3) + 3 * (x + 1 / x) := by
      field_simp; ring
    rw [h₀] at h
    norm_num at h
    simp only [one_div] at h ⊢
    linarith
  have e4 : x ^ 4 + 1 / x ^ 4 = 47 := by
    have h : (x + 1 / x) * (x ^ 3 + 1 / x ^ 3)
        = (x ^ 4 + 1 / x ^ 4) + (x ^ 2 + 1 / x ^ 2) := by field_simp; ring
    rw [h₀, e3, e2] at h
    linarith
  have e5 : x ^ 5 + 1 / x ^ 5 = 123 := by
    have h : (x + 1 / x) * (x ^ 4 + 1 / x ^ 4)
        = (x ^ 5 + 1 / x ^ 5) + (x ^ 3 + 1 / x ^ 3) := by field_simp; ring
    rw [h₀, e4, e3] at h
    linarith
  have e6 : x ^ 6 + 1 / x ^ 6 = 322 := by
    have h : (x + 1 / x) * (x ^ 5 + 1 / x ^ 5)
        = (x ^ 6 + 1 / x ^ 6) + (x ^ 4 + 1 / x ^ 4) := by field_simp; ring
    rw [h₀, e5, e4] at h
    linarith
  have e7 : x ^ 7 + 1 / x ^ 7 = 843 := by
    have h : (x + 1 / x) * (x ^ 6 + 1 / x ^ 6)
        = (x ^ 7 + 1 / x ^ 7) + (x ^ 5 + 1 / x ^ 5) := by field_simp; ring
    rw [h₀, e6, e5] at h
    linarith
  have e8 : x ^ 8 + 1 / x ^ 8 = 2207 := by
    have h : (x + 1 / x) * (x ^ 7 + 1 / x ^ 7)
        = (x ^ 8 + 1 / x ^ 8) + (x ^ 6 + 1 / x ^ 6) := by field_simp; ring
    rw [h₀, e7, e6] at h
    linarith
  have e9 : x ^ 9 + 1 / x ^ 9 = 5778 := by
    have h : (x + 1 / x) * (x ^ 8 + 1 / x ^ 8)
        = (x ^ 9 + 1 / x ^ 9) + (x ^ 7 + 1 / x ^ 7) := by field_simp; ring
    rw [h₀, e8, e7] at h
    linarith
  have hr3 : r ^ 3 = x ^ 9 := by
    rw [← hx3]; ring
  calc r ^ 3 + 1 / r ^ 3 = x ^ 9 + 1 / x ^ 9 := by rw [hr3]
    _ = 5778 := e9
