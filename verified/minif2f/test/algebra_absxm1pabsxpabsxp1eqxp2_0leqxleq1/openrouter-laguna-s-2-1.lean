import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  by_cases h1 : x ≥ 1
  · -- Case 1: x ≥ 1
    have h_abs1 : abs (x - 1) = x - 1 := abs_of_nonneg (sub_nonneg_of_le h1)
    have h_abs2 : abs x = x := abs_of_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one h1))
    have h_abs3 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
    rw [h_abs1, h_abs2, h_abs3] at h₀
    have h_eq : x = 1 := by linarith
    subst h_eq
    exact ⟨by norm_num, by norm_num⟩
  · -- Case 2: x < 1
    by_cases h2 : x ≥ 0
    · -- Case 2a: 0 ≤ x < 1
      have h_abs1 : abs (x - 1) = 1 - x := by
        have : x - 1 ≤ 0 := by linarith
        rw [abs_of_nonpos this, neg_sub]
      have h_abs2 : abs x = x := abs_of_nonneg h2
      have h_abs3 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
      rw [h_abs1, h_abs2, h_abs3] at h₀
      exact ⟨h2, le_of_lt (not_le.mp h1)⟩
    · -- Case 2b: x < 0
      by_cases h3 : x ≥ -1
      · -- Case 2b-i: -1 ≤ x < 0
        have h_abs1 : abs (x - 1) = 1 - x := by
          have : x - 1 ≤ 0 := by linarith
          rw [abs_of_nonpos this, neg_sub]
        have h_abs2 : abs x = -x := abs_of_nonpos (le_of_lt (not_le.mp h2))
        have h_abs3 : abs (x + 1) = x + 1 := abs_of_nonneg (by linarith)
        rw [h_abs1, h_abs2, h_abs3] at h₀
        have h_eq : x = 0 := by linarith
        subst h_eq
        exfalso
        linarith
      · -- Case 2b-ii: x < -1
        have h_abs1 : abs (x - 1) = 1 - x := by
          have : x - 1 ≤ 0 := by linarith
          rw [abs_of_nonpos this, neg_sub]
        have h_abs2 : abs x = -x := abs_of_nonpos (le_of_lt (not_le.mp h2))
        have h_abs3 : abs (x + 1) = -(x + 1) := by
          have : x + 1 ≤ 0 := by linarith
          rw [abs_of_nonpos this, neg_add]
        rw [h_abs1, h_abs2, h_abs3] at h₀
        have h_eq : x = -1 / 2 := by linarith
        subst h_eq
        exfalso
        linarith
