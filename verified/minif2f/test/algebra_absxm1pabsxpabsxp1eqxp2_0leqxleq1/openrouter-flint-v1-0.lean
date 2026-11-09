import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have hsum_ge : 2 ≤ abs (x - 1) + abs (x + 1) := by
    have h := abs_sub (x - 1) (x + 1)
    have hsub : (x - 1) - (x + 1) = -2 := by ring
    rw [hsub] at h
    norm_num at h
    exact h
  have hx_le : abs x ≤ x := by
    have hEq : abs x + (abs (x - 1) + abs (x + 1)) = x + 2 := by
      linarith
    have hle : abs x + 2 ≤ x + 2 := by
      calc
        abs x + 2 ≤ abs x + (abs (x - 1) + abs (x + 1)) := by linarith
        _ = x + 2 := hEq
    linarith
  have hx_nonneg : 0 ≤ x := by
    by_contra hnot
    have hx_neg : x < 0 := lt_of_not_ge hnot
    have habs : abs x = -x := abs_of_neg hx_neg
    rw [habs] at hx_le
    linarith
  have hx_abs : abs x = x := abs_of_nonneg hx_nonneg
  have h₀' : abs (x - 1) + x + abs (x + 1) = x + 2 := by
    rw [hx_abs] at h₀
    exact h₀
  have hsum : abs (x - 1) + abs (x + 1) = 2 := by
    linarith
  have hx1_nonneg : 0 ≤ x + 1 := by linarith
  have habsx1 : abs (x + 1) = x + 1 := abs_of_nonneg hx1_nonneg
  have hsum2 : abs (x - 1) = 1 - x := by
    linarith
  have hx_le_one : x ≤ 1 := by
    have hle_abs : 0 ≤ abs (x - 1) := abs_nonneg _
    have : 0 ≤ 1 - x := by linarith
    linarith
  exact ⟨hx_nonneg, hx_le_one⟩
