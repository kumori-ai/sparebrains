import Mathlib

open scoped Nat
open scoped Real

/--
If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. -/
theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = 121 / 25 := by
  have ha_pos : (0 : ℝ) < (11 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have ha_nonneg : (0 : ℝ) ≤ (11 : ℝ) ^ (1 / 4 : ℝ) := ha_pos.le
  have h8 : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (8 : ℝ) = 121 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 11)]
    have hmul : (1 / 4 : ℝ) * 8 = 2 := by norm_num
    rw [hmul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2 : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (2 * (3 * x - 3)) = (1 / 5 : ℝ) ^ (2 : ℝ) := by
    have hcomm : (2 : ℝ) * (3 * x - 3) = (3 * x - 3) * 2 := by ring
    rw [hcomm, Real.rpow_mul ha_nonneg (3 * x - 3) 2, h]
  have hsplit : (6 * x + 2 : ℝ) = 2 * (3 * x - 3) + 8 := by ring
  rw [hsplit, Real.rpow_add ha_pos, h2, h8, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num
