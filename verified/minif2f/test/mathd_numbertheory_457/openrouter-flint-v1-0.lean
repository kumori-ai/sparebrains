import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  unfold IsLeast
  constructor
  · norm_num
  · intro n hn
    rcases hn with ⟨hn_pos, hn_dvd⟩
    have h17_dvd_fact : 17 ∣ Nat.factorial n := by
      exact dvd_trans (by norm_num : 17 ∣ 80325) hn_dvd
    have hp : Nat.Prime 17 := by decide
    have hfact : 17 ≤ n := (Nat.Prime.dvd_factorial hp).mp h17_dvd_fact
    exact hfact
