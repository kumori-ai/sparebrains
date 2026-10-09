import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex06 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp [Finset.mem_sdiff, Finset.mem_union, and_assoc]
