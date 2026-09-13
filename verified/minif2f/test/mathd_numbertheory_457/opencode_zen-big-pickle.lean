import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  constructor
  · constructor
    · norm_num
    · norm_num [Nat.factorial]
  · intro n hn
    rcases hn with ⟨hnpos, hdiv⟩
    have h17_prime : Nat.Prime 17 := by norm_num
    have h17 : 17 ∣ 80325 := by norm_num
    have h17_div : 17 ∣ n ! := dvd_trans h17 hdiv
    exact (Nat.Prime.dvd_factorial h17_prime).mp h17_div
