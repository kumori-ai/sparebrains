import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest positive integer $N$ such that the value $7 + (30 \times N)$ is not a prime number? -/
theorem mathd_numbertheory_150 : IsLeast {n | ¬Nat.Prime (7 + 30 * n)} 6 := by
  constructor
  · intro hprime
    have hdvd : (11 : ℕ) ∣ (7 + 30 * 6) := by norm_num
    have h := hprime.eq_one_or_self_of_dvd 11 hdvd
    norm_num at h
  · intro n hn
    by_contra hlt
    push_neg at hlt
    interval_cases n <;> exact hn (by norm_num)
