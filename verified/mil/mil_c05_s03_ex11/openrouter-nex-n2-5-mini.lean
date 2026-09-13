import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex11 (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  intro h
  obtain ⟨s, hs⟩ := h
  use s.sum id + 1
  intro k hk
  have hks : k ∈ s := hs k hk
  have hle : k ≤ s.sum id := Finset.single_le_sum (fun x hx => Nat.zero_le x) hks
  exact Nat.lt_of_le_of_lt hle (Nat.lt_succ_self _)
