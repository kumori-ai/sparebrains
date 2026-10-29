import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have h2gt1 : 1 < (2 : ℝ) := by norm_num
  have h5gt1 : 1 < (5 : ℝ) := by norm_num
  have h32_eq : (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
  have h125_eq : (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
  have ha_eq_5 : a = 5 := by
    rw [h32_eq] at h₀
    have hmono := Real.strictMono_rpow_of_base_gt_one h2gt1
    exact hmono.injective h₀
  have hb_eq_3 : b = 3 := by
    rw [ha_eq_5] at h₁
    rw [h125_eq] at h₁
    have hmono := Real.strictMono_rpow_of_base_gt_one h5gt1
    exact hmono.injective h₁
  rw [ha_eq_5, hb_eq_3]
  norm_num
