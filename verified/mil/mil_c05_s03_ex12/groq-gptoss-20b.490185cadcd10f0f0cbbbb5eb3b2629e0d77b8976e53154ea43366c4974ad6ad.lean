import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).filter Q, ?_⟩
  intro k
  constructor
  · intro hk
    have hk_le : k ≤ n := hn k hk
    have hk_lt : k < n + 1 := Nat.lt_succ_of_le hk_le
    have hk_mem_range : k ∈ Finset.range (n + 1) := by
      exact Finset.mem_range.mpr hk_lt
    exact Finset.mem_filter.mpr ⟨hk_mem_range, hk⟩
  · intro hk
    have hk_mem_filter := hk
    have hk_Q : Q k := (Finset.mem_filter.mp hk_mem_filter).2
    exact hk_Q
