import Mathlib

open Finset

/-- Mathematics in Lean, Chapter 6 §2 (Counting Arguments), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c06_s02_ex03 {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have coprime_succ : ∀ a : ℕ, Nat.Coprime a (a + 1) := by
    intro a
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec]
    by_cases ha0 : a = 0
    · subst ha0; simp
    by_cases ha1 : a = 1
    · subst ha1; simp
    have hmod : (a + 1) % a = 1 := by
      have h1 : a + 1 = 1 + a := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < a)]
    rw [hmod]
    simp
  obtain ⟨m, hmA, k, hkA, hmk_ne, hmk_div⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := A) (t := range n) (f := fun x => x / 2)
      (by simp [hA])
      (by
        intro x hx
        have hx2 : x < 2 * n := by
          have h := hA' hx
          simp only [mem_range] at h
          exact h
        show x / 2 ∈ range n
        simp only [mem_range]
        omega)
  refine ⟨m, hmA, k, hkA, ?_⟩
  rcases lt_or_gt_of_ne hmk_ne with h | h
  · have hk : k = m + 1 := by omega
    subst hk
    exact coprime_succ m
  · have hm : m = k + 1 := by omega
    subst hm
    exact (coprime_succ k).symm
