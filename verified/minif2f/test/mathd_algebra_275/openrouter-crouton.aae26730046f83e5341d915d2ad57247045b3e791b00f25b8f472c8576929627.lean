import Mathlib

open scoped Nat
open scoped Real

/--
If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. -/
theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = 121 / 25 := by
  have ha_pos : 0 < (11 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have ha_nonneg : 0 ≤ (11 : ℝ) ^ (1 / 4 : ℝ) := le_of_lt ha_pos
  have h8 : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (8 : ℝ) = 121 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 11)]
    have hmul : (1 / 4 : ℝ) * 8 = 2 := by norm_num
    rw [hmul]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hsq : ((1 / 5 : ℝ) ^ (2 : ℝ)) = 1 / 25 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h_eq : 6 * x + 2 = (3 * x - 3) * 2 + 8 := by ring
  rw [h_eq, Real.rpow_add ha_pos, Real.rpow_mul ha_nonneg, h, h8, hsq]
  norm_num
