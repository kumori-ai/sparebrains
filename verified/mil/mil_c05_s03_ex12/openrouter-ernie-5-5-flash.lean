import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).filter Q, fun k => ?_⟩
  rw [Finset.mem_filter]
  constructor
  · intro hQ
    have hk : k ≤ n := hn k hQ
    exact ⟨Finset.mem_range.mpr (by omega), hQ⟩
  · intro h
    exact h.2
