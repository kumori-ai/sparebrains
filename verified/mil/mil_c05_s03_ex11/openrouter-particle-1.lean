import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex11 (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  refine ⟨s.sup id + 1, ?_⟩
  intro k hk
  have hks : k ∈ s := hs k hk
  have hle : k ≤ s.sup id := by
    simpa using (Finset.le_sup (s := s) (f := id) hks)
  exact Nat.lt_succ_of_le hle
