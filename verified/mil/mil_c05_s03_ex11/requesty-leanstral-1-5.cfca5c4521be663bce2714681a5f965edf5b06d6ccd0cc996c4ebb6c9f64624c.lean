import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex11 (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, h⟩
  refine ⟨s.sup id + 1, λ k hk => ?_⟩
  have hk_mem : k ∈ s := h k hk
  have hk_le_sup : k ≤ s.sup id := Finset.le_sup (f := id) hk_mem
  exact Nat.lt_succ_of_le hk_le_sup
