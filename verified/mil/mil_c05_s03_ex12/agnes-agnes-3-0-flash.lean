import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h_bound
  obtain ⟨n, h_bound_n⟩ := h_bound
  use (Finset.Icc 0 n).filter Q
  intro k
  constructor
  · intro hk
    have h_le : k ≤ n := h_bound_n k hk
    have h_ge : 0 ≤ k := by
      apply Nat.zero_le
    have h_mem_Icc : k ∈ Finset.Icc 0 n := Finset.mem_Icc.mpr ⟨h_ge, h_le⟩
    have h_mem_filter : k ∈ (Finset.Icc 0 n).filter Q := Finset.mem_filter.mpr ⟨h_mem_Icc, hk⟩
    exact h_mem_filter
  · intro hk
    have h_mem_Icc : k ∈ Finset.Icc 0 n := (Finset.mem_filter.mp hk).1
    have hk : Q k := (Finset.mem_filter.mp hk).2
    exact hk
