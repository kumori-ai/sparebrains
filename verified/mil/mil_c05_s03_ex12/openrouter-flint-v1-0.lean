import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  refine ⟨Finset.filter (fun k => Q k) (Finset.range (n + 1)), ?_⟩
  intro k
  rw [Finset.mem_filter]
  constructor
  · intro hQk
    have hkn : k ≤ n := hn k hQk
    exact ⟨Finset.mem_range.mpr (by omega), hQk⟩
  · intro h
    exact h.2
