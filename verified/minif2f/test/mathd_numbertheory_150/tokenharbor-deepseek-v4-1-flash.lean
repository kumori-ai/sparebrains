import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest positive integer $N$ such that the value $7 + (30 \times N)$ is not a prime number? -/
theorem mathd_numbertheory_150 : IsLeast {n | ¬Nat.Prime (7 + 30 * n)} 6 := by
  constructor
  · norm_num
  · intro n hn
    by_contra h
    have hnlt : n < 6 := by omega
    interval_cases n <;> exact hn (by norm_num)
