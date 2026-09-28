import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  rcases lt_or_eq_of_le h with hab | hba
  · apply le_of_lt
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · simpa [add_comm] using add_lt_add_left (exp_lt_exp.mpr hab) 1
  · subst b
    rfl
