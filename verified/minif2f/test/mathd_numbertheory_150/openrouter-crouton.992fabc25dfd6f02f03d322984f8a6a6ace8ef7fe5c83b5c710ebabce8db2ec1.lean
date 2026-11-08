import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest positive integer $N$ such that the value $7 + (30 \times N)$ is not a prime number? -/
theorem mathd_numbertheory_150 : IsLeast {n | ¬Nat.Prime (7 + 30 * n)} 6 := by
  constructor
  · show ¬Nat.Prime (7 + 30 * 6)
    norm_num
  · intro n hn
    have hn' : ¬Nat.Prime (7 + 30 * n) := hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> exact absurd (by norm_num) hn'
    · exact h
