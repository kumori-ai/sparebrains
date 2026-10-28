import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨(Finset.range (n+1)).filter Q, λ k => ?_⟩
  constructor
  · intro hq
    have hk : k ≤ n := hn k hq
    have hk_lt : k < n+1 := Nat.lt_succ_of_le hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, hq⟩
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
