import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  refine' ⟨by norm_num, fun n hn => _⟩
  by_contra h
  have h₁ : n ≤ 16 := by omega
  interval_cases n <;> norm_num at hn
