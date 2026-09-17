import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $129^{34}+96^{38}$ is divided by $11$? -/
theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
  norm_num
