import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  let s := (range (n+1)).filter Q
  refine ⟨s, ?_⟩
  intro k
  constructor
  · intro hk
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, hk⟩
    have hk_le_n := hn k hk
    omega
  · intro hk
    exact (mem_filter.mp hk).2
