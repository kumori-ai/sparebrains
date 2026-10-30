import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use Finset.filter (fun k => Q k) (Finset.range (n + 1))
  intro k
  constructor
  · intro h
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(Nat.lt_succ_iff).mpr (hn k h), h⟩
  · intro h
    rw [Finset.mem_filter, Finset.mem_range] at h
    exact h.2
