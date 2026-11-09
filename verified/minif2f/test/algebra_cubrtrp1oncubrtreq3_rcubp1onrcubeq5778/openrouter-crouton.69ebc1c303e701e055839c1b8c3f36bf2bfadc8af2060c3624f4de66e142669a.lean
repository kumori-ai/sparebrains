import Mathlib

open scoped Nat
open scoped Real

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3)
    (h₁ : 0 < r) : r ^ 3 + 1 / r ^ 3 = 5778 := by
  set x := r ^ ((1 : ℝ) / 3) with hx_def
  have hx_pos : 0 < x := Real.rpow_pos_of_pos h₁ _
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hr_eq : r = x ^ 3 := by
    have h : x ^ (3 : ℕ) = r := by
      rw [hx_def, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h₁)]
      have e : (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 := by norm_num
      rw [e, Real.rpow_one]
    exact h.symm
  have hid : x ^ 9 + 1 / x ^ 9
      = (x + 1 / x) ^ 9 - 9 * (x + 1 / x) ^ 7 + 27 * (x + 1 / x) ^ 5
        - 30 * (x + 1 / x) ^ 3 + 9 * (x + 1 / x) := by
    field_simp
    ring
  rw [hr_eq]
  have h9 : (x ^ 3) ^ 3 = x ^ 9 := by ring
  rw [h9, hid, h₀]
  norm_num
