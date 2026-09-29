import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  constructor
  · norm_num [Nat.factorial]
  · rintro n ⟨hn_pos, hn_div⟩
    by_contra h_not_le
    have h_lt : n < 17 := by omega
    interval_cases n <;> norm_num [Nat.factorial] at hn_div
