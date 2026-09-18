import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro hn
  cases hn with
  | intro n hn =>
    use Finset.filter Q (Finset.Icc 0 n)
    intro k
    constructor
    · intro hq
      have hbound : k ≤ n := hn k hq
      have hmem : k ∈ Finset.Icc 0 n := by
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hbound⟩
      exact Finset.mem_filter.mpr ⟨hmem, hq⟩
    · intro hks
      exact (Finset.mem_filter.mp hks).right
