import Mathlib

open scoped Nat
open scoped Real

/-- How many integers are in the solution set of $|x-2|\leq5.6$ ? -/
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have hbound : (5 : ℤ) + 6 / 10 = 5 := by norm_num
  have hchar (n : ℤ) :
      abs (n - 2) ≤ 5 + 6 / 10 ↔ -3 ≤ n ∧ n ≤ 7 := by
    rw [hbound, abs_le]
    omega
  have hS : S = {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} := by
    ext n
    rw [h₀ n, hchar n]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hS]
  simp
