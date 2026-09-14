import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  obtain ⟨N, hN⟩ := h
  use (range (N + 1)).filter Q
  intro k
  constructor
  · intro hk
    have hk' : k ≤ N := hN k hk
    rw [mem_filter, mem_range]
    constructor
    · linarith
    · exact hk
  · intro hk
    exact (mem_filter.1 hk).2
