import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have h2gt1 : (1 : ℝ) < 2 := by norm_num
  have h5gt1 : (1 : ℝ) < 5 := by norm_num
  have hmono2 := Real.strictMono_rpow_of_base_gt_one h2gt1
  have hmono5 := Real.strictMono_rpow_of_base_gt_one h5gt1
  have ha_eq_5 : a = 5 := by
    apply hmono2.injective
    calc
      (2 : ℝ) ^ a = 32 := h₀
      _ = (2 : ℝ) ^ (5 : ℝ) := by norm_num
  have hb_eq_3 : b = 3 := by
    apply hmono5.injective
    calc
      (5 : ℝ) ^ b = 125 := by simpa [ha_eq_5] using h₁
      _ = (5 : ℝ) ^ (3 : ℝ) := by norm_num
  calc
    b ^ a = (3 : ℝ) ^ (5 : ℝ) := by simp [ha_eq_5, hb_eq_3]
    _ = 243 := by norm_num
