import Mathlib

open scoped Nat
open scoped Real

/--
If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. -/
theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = 121 / 25 := by
  have ha : (0 : ℝ) < (11 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have ha8 : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (8 : ℝ) = 121 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 11),
      show (1 / 4 : ℝ) * 8 = 2 by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hsq : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (2 * (3 * x - 3)) = (1 / 5 : ℝ) ^ 2 := by
    rw [mul_comm (2 : ℝ) (3 * x - 3), Real.rpow_mul ha.le, h,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2)
      = ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (2 * (3 * x - 3)) *
          ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (8 : ℝ) := by
        rw [show 6 * x + 2 = 2 * (3 * x - 3) + 8 by ring, Real.rpow_add ha]
    _ = (1 / 5 : ℝ) ^ 2 * 121 := by rw [hsq, ha8]
    _ = 121 / 25 := by norm_num
