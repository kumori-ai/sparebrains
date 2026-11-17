import Mathlib

open scoped Nat
open scoped Real

/-- How many integers are in the solution set of $|x-2|\leq5.6$ ? -/
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have hS : S = Finset.Icc (-3 : ℤ) 7 := by
    ext n
    rw [h₀ n]
    simp only [Finset.mem_Icc]
    norm_num
    rw [abs_le]
    omega
  have hIcc : Finset.Icc (-3 : ℤ) 7 = ({-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} : Finset ℤ) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hS, hIcc]
  decide
