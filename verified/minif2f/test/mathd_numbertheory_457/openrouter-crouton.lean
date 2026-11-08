import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  constructor
  · refine ⟨by norm_num, by decide⟩
  · intro n hn
    obtain ⟨hpos, hdvd⟩ := hn
    by_contra h
    have hlt : n < 17 := by omega
    interval_cases n <;> exact absurd hdvd (by decide)
