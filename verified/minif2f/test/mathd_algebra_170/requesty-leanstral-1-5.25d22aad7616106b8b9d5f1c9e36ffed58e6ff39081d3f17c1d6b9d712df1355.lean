import Mathlib

open scoped Nat
open scoped Real

/-- How many integers are in the solution set of $|x-2|\leq5.6$ ? -/
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have hS : S = Finset.Icc (-3 : ℤ) 7 := by
    ext n
    rw [h₀ n]
    have h5 : (5 : ℤ) + 6 / 10 = (5 : ℤ) := by norm_num
    rw [h5]
    by_cases h : n - 2 ≥ 0
    · have habs : abs (n - 2) = n - 2 := abs_of_nonneg h
      rw [habs]
      constructor
      · intro hineq
        have hnle7 : n ≤ 7 := by omega
        have hnge_3 : -3 ≤ n := by omega
        exact Finset.mem_Icc.mpr ⟨hnge_3, hnle7⟩
      · intro hmem
        rcases Finset.mem_Icc.mp hmem with ⟨hlo, hhi⟩
        omega
    · have hneg : n - 2 < 0 := by omega
      have habs : abs (n - 2) = -(n - 2) := abs_of_neg hneg
      rw [habs]
      constructor
      · intro hineq
        have hnle7 : n ≤ 7 := by omega
        have hnge_3 : -3 ≤ n := by omega
        exact Finset.mem_Icc.mpr ⟨hnge_3, hnle7⟩
      · intro hmem
        rcases Finset.mem_Icc.mp hmem with ⟨hlo, hhi⟩
        omega
  rw [hS]
  decide
