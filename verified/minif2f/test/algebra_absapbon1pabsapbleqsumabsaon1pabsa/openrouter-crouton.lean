import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have hpos1 : (0 : ℝ) < 1 + abs a := by linarith [abs_nonneg a]
  have hpos2 : (0 : ℝ) < 1 + abs b := by linarith [abs_nonneg b]
  have hpos3 : (0 : ℝ) < 1 + abs (a + b) := by linarith [abs_nonneg (a + b)]
  have htri : abs (a + b) ≤ abs a + abs b := abs_add_le a b
  have hY : (0 : ℝ) < (1 + abs a) * (1 + abs b) := mul_pos hpos1 hpos2
  rw [div_add_div _ _ (ne_of_gt hpos1) (ne_of_gt hpos2),
      le_div_iff₀ hY, div_mul_eq_mul_div, div_le_iff₀ hpos3]
  nlinarith [htri, abs_nonneg a, abs_nonneg b, abs_nonneg (a + b),
    mul_nonneg (abs_nonneg a) (abs_nonneg b),
    mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b)) (abs_nonneg (a + b)),
    mul_nonneg (abs_nonneg a) (abs_nonneg (a + b)),
    mul_nonneg (abs_nonneg b) (abs_nonneg (a + b))]
