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
    have hn6 : n < 6 := Nat.lt_of_not_ge h
    interval_cases n <;> norm_num at hn
