import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp [mem_union, mem_inter]
  tauto
