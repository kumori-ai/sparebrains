import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  obtain ⟨n, hn⟩ := h
  use (Finset.range (n+1)).filter Q
  intro k
  constructor
  · intro hQ
    rw [Finset.mem_filter]
    exact ⟨by
      rw [Finset.mem_range]
      exact Nat.lt_of_le_of_lt (hn k hQ) (Nat.lt_succ_self n)
    , hQ⟩
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
