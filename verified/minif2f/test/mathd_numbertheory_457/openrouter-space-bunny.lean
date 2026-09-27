import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  constructor
  · norm_num [Nat.factorial]
  · rintro n ⟨hn0, hn⟩
    by_contra hn17
    have hnlt : n < 17 := by omega
    interval_cases n <;> norm_num [Nat.factorial] at hn
