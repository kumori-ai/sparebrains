import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  refine ⟨Finset.filter Q (Finset.range (n + 1)), ?_⟩
  intro k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hk
    have h := hn k hk
    exact ⟨by omega, hk⟩
  · intro hk
    exact hk.2
