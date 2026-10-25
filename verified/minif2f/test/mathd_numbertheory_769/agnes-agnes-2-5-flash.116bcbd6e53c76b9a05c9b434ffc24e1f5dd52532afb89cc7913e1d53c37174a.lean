import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $129^{34}+96^{38}$ is divided by $11$? -/
theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
  norm_num [pow_succ, pow_zero, pow_one, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
