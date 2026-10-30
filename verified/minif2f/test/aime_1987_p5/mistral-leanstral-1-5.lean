import Mathlib

open scoped Nat
open scoped Real

/-- Find $3x^2 y^2$ if $x$ and $y$ are integers such that $y^2 + 3x^2 y^2 = 30x^2 + 517$. -/
theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  -- Rearrange equation to (y^2 - 10)*(1 + 3*x^2) = 507
  have h_prod : (y ^ 2 - 10) * (1 + 3 * x ^ 2) = 507 := by
    calc
      (y ^ 2 - 10) * (1 + 3 * x ^ 2) = (y ^ 2 * (1 + 3 * x ^ 2)) - 10 * (1 + 3 * x ^ 2) := by ring
      _ = (y ^ 2 + 3 * (x ^ 2 * y ^ 2)) - 10 * (1 + 3 * x ^ 2) := by ring
      _ = (30 * x ^ 2 + 517) - 10 * (1 + 3 * x ^ 2) := by rw [h₀]
      _ = 507 := by ring
  have h_pos : 0 < 1 + 3 * x ^ 2 := by
    have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have h_dvd : (1 + 3 * x ^ 2) ∣ (507 : ℤ) := by
    rw [← h_prod]
    exact ⟨y ^ 2 - 10, by ring⟩
  have h_le : 1 + 3 * x ^ 2 ≤ 507 := by
    exact Int.le_of_dvd (by norm_num : 0 < (507 : ℤ)) h_dvd
  have hx_sq_le : x ^ 2 ≤ 168 := by
    linarith
  have hx_lower : -12 ≤ x := by
    by_contra! h
    have hx' : x ≤ -13 := by omega
    nlinarith
  have hx_upper : x ≤ 12 := by
    by_contra! h
    have hx' : 13 ≤ x := by omega
    nlinarith
  have hy_sq_le : y ^ 2 ≤ 517 := by
    by_contra! h
    nlinarith
  have hy_lower : -22 ≤ y := by
    by_contra! h
    have hy' : y ≤ -23 := by omega
    nlinarith
  have hy_upper : y ≤ 22 := by
    by_contra! h
    have hy' : 23 ≤ y := by omega
    nlinarith
  have hx_mem : x ∈ Finset.Icc (-12 : ℤ) 12 :=
    Finset.mem_Icc.mpr ⟨hx_lower, hx_upper⟩
  have hy_mem : y ∈ Finset.Icc (-22 : ℤ) 22 :=
    Finset.mem_Icc.mpr ⟨hy_lower, hy_upper⟩
  have h_all : ∀ x' ∈ Finset.Icc (-12 : ℤ) 12, ∀ y' ∈ Finset.Icc (-22 : ℤ) 22,
      (y' ^ 2 + 3 * (x' ^ 2 * y' ^ 2) = 30 * x' ^ 2 + 517) → (3 * (x' ^ 2 * y' ^ 2) = 588) := by
    decide
  exact h_all x hx_mem y hy_mem h₀
