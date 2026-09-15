import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $5^{30}$ is divided by 7? -/
theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by
  have h : 5 ^ 6 % 7 = 1 := by norm_num
  have h2 : 5 ^ 30 = (5 ^ 6) ^ 5 := by simp [Nat.pow_mul]
  rw [h2]
  have h3 : (5 ^ 6) ^ 5 % 7 = (5 ^ 6 % 7) ^ 5 % 7 := by
    apply Nat.pow_mod
  rw [h3, h]
  norm_num
