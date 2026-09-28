import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex11 (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  by_cases h : s.Nonempty
  · refine ⟨s.max' h + 1, ?_⟩
    intro k hk
    have hks : k ∈ s := hs k hk
    have hle : k ≤ s.max' h := Finset.le_max' s k hks
    omega
  · refine ⟨0, ?_⟩
    intro k hk
    have hks : k ∈ s := hs k hk
    exact (h ⟨k, hks⟩).elim
