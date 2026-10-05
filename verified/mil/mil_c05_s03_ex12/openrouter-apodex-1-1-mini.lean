import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use Finset.filter Q (Finset.range (n + 1))
  intro k
  constructor
  · intro hq
    have hbound : k ≤ n := hn k hq
    have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hbound)
    exact Finset.mem_filter.mpr ⟨hmem, hq⟩
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
