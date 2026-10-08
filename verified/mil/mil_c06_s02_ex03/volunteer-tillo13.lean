import Mathlib

open Finset

/-- Mathematics in Lean, Chapter 6 §2 (Counting Arguments), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c06_s02_ex03 {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have hmaps : ∀ a ∈ A, a / 2 ∈ range n := by
    intro a ha
    have ha' := mem_range.mp (hA' ha)
    apply mem_range.mpr
    omega
  have hcard : #(range n) < #A := by
    simp [hA]
  obtain ⟨x, hx, y, hy, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hconsecutive : x + 1 = y ∨ y + 1 = x := by
    omega
  rcases hconsecutive with h | h
  · refine ⟨x, hx, y, hy, ?_⟩
    rw [← h]
    simp
  · refine ⟨y, hy, x, hx, ?_⟩
    rw [← h]
    simp
