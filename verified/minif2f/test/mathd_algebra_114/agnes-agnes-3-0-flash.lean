import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  subst h₀
  norm_num [Real.rpow_def_of_pos, Real.rpow_pos_of_pos]
  <;> ring_nf
  <;> norm_num
