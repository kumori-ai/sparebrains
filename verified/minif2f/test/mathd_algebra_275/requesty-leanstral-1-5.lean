import Mathlib

open scoped Nat
open scoped Real

/--
If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. -/
theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = 121 / 25 := by
  set a := (11 : ℝ) ^ (1 / 4 : ℝ) with ha
  have ha_pos : a > 0 := by
    rw [ha]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 11) (1 / 4 : ℝ)
  have h8 : a ^ (8 : ℝ) = (121 : ℝ) := by
    calc
      a ^ (8 : ℝ) = ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (8 : ℝ) := by rw [ha]
      _ = (11 : ℝ) ^ ((1 / 4 : ℝ) * (8 : ℝ)) := by
        rw [Real.rpow_mul (show (11 : ℝ) ≥ 0 from by norm_num) (1 / 4 : ℝ) (8 : ℝ)]
      _ = (11 : ℝ) ^ (2 : ℝ) := by ring
      _ = (11 : ℝ) ^ 2 := by rw [Real.rpow_two]
      _ = (121 : ℝ) := by norm_num
  calc
    ((11 : ℝ) ^ (1 / 4 : ℝ)) ^ (6 * x + 2) = a ^ (6 * x + 2) := by rw [ha]
    _ = a ^ (2 * (3 * x - 3) + 8) := by rw [show (6 * x + 2 : ℝ) = 2 * (3 * x - 3) + 8 by ring]
    _ = a ^ (2 * (3 * x - 3)) * a ^ (8 : ℝ) := by rw [Real.rpow_add ha_pos (2 * (3 * x - 3)) (8 : ℝ)]
    _ = a ^ ((3 * x - 3) * 2) * a ^ (8 : ℝ) := by rw [show (2 * (3 * x - 3) : ℝ) = (3 * x - 3) * 2 by ring]
    _ = ((a ^ (3 * x - 3)) ^ (2 : ℝ)) * a ^ (8 : ℝ) := by
      rw [← Real.rpow_mul ha_pos.le (3 * x - 3) (2 : ℝ)]
    _ = ((1 / 5) ^ (2 : ℝ)) * a ^ (8 : ℝ) := by rw [h]
    _ = ((1 / 5) ^ 2) * a ^ (8 : ℝ) := by rw [Real.rpow_two]
    _ = (1 / 25) * a ^ (8 : ℝ) := by norm_num
    _ = (1 / 25) * (121 : ℝ) := by rw [h8]
    _ = 121 / 25 := by norm_num
