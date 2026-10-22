import Mathlib

open scoped Nat
open scoped Real

/-- How many integers are in the solution set of $|x-2|\leq5.6$ ? -/
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have hbound : (5 : ℤ) + 6 / 10 = 5 := by
    norm_num
  have hmem (n : ℤ) : n ∈ S ↔ -3 ≤ n ∧ n ≤ 7 := by
    rw [h₀ n, hbound, abs_le]
    omega
  have hS : S = {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} := by
    ext n
    constructor
    · intro hn
      have hn' := (hmem n).mp hn
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · intro hn
      apply (hmem n).mpr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
  rw [hS]
  simp
