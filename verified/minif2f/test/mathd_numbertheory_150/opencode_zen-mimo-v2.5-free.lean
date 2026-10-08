import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest positive integer $N$ such that the value $7 + (30 \times N)$ is not a prime number? -/
theorem mathd_numbertheory_150 : IsLeast {n | ¬Nat.Prime (7 + 30 * n)} 6 := by
  constructor
  · -- Show 6 is in the set: 7 + 30*6 = 187, not prime.
    show ¬Nat.Prime (7 + 30 * 6)
    norm_num
  · -- Show any n in the set is at least 6.
    intro n hn
    by_contra h
    push_neg at h
    -- h : n < 6
    have hp : ∀ m < 6, Nat.Prime (7 + 30 * m) := by
      intro m hm
      interval_cases m <;> norm_num [Nat.prime_def_lt]
    exact absurd (hp n h) hn
