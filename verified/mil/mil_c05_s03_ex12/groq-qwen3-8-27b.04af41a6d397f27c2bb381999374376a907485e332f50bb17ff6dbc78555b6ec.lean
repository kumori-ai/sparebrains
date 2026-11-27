import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  obtain ⟨n, hn⟩ := h
  use (Finset.range (n + 1)).filter Q
  intro k
  constructor
  · intro hQ
    have hk : k ≤ n := hn k hQ
    have hmem : k ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      omega
    exact Finset.mem_filter.mpr ⟨hmem, hQ⟩
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
