import Mathlib

open scoped Nat
open scoped Real

/-- How many integers between 15 and 85 are divisible by 20? -/
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
  have h : Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85) = {20, 40, 60, 80} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, hk⟩
      have hk1 : 1 ≤ k := by omega
      have hk2 : k ≤ 4 := by omega
      interval_cases k <;> omega
    · rintro (rfl | rfl | rfl | rfl) <;> norm_num
  rw [h]
  first
    | decide
    | simp
    | rfl
