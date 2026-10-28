import Mathlib

open scoped Nat
open scoped Real

/-- How many integers are in the solution set of $|x-2|\leq5.6$ ? -/
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have hS : S = (Finset.Icc (-3 : ℤ) 7).filter (λ n => abs (n - 2) ≤ 5 + 6 / 10) := by
    ext n
    constructor
    · intro hn
      rw [h₀ n] at hn
      have hbound : abs (n - 2) ≤ 5 := by
        omega
      rcases abs_le.mp hbound with ⟨h1, h2⟩
      have hlo : (-3 : ℤ) ≤ n := by omega
      have hhi : n ≤ 7 := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hn⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hncond⟩
      rw [h₀ n]
      exact hncond
  rw [hS]
  decide
