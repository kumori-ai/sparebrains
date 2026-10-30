import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex11 (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, h⟩
  by_cases hne : s.Nonempty
  · let m := s.max' hne
    use m + 1
    intro k hk
    have hmem : k ∈ s := h k hk
    have hle : k ≤ m := Finset.le_max' s k hmem
    exact Nat.lt_succ_of_le hle
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    use 0
    intro k hk
    have hmem : k ∈ s := h k hk
    rw [hempty] at hmem
    exact absurd hmem (by simp)
