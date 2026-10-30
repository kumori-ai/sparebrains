import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨(range (n+1)).filter Q, λ k => ?_⟩
  constructor
  · intro hq
    have hk_le_n : k ≤ n := hn k hq
    have hk_lt_succ : k < n+1 := Nat.lt_succ_of_le hk_le_n
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt_succ, hq⟩
  · intro hmem
    rcases Finset.mem_filter.mp hmem with ⟨_, hq⟩
    exact hq
