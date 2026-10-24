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
    by_contra h
    push_neg at h
    have h₃ : n ≤ 5 := by omega
    have h₄ : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
      omega
    rcases h₄ with (rfl | rfl | rfl | rfl | rfl | rfl)
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
