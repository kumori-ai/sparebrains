import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $5^{30}$ is divided by 7? -/
theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by
  norm_num [pow_succ, pow_zero, pow_one, Nat.mul_mod, Nat.pow_mod]
