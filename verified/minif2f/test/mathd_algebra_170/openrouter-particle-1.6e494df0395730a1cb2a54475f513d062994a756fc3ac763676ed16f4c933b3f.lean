import Mathlib

open scoped Nat
open scoped Real

/-- How many integers are in the solution set of $|x-2|\leq5.6$ ? -/
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have hS : S = Finset.Icc (-3 : ℤ) 7 := by
    ext n
    rw [h₀ n]
    norm_num
    rw [abs_le]
    simp [Finset.mem_Icc]
    omega
  rw [hS]
  decide
