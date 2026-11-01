import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $\sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}$? -/
theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  norm_num
