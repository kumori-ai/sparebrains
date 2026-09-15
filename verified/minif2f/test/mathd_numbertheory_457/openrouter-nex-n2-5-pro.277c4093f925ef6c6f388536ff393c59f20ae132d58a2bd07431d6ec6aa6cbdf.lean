import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  refine ⟨by norm_num [Nat.factorial], ?_⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  rcases hn with ⟨hnpos, hdiv⟩
  by_contra h
  have h17 : 17 ∣ n ! := dvd_trans (by norm_num) hdiv
  rw [Nat.Prime.dvd_factorial (by norm_num)] at h17
  exact h h17
