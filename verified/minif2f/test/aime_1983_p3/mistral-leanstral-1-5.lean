import Mathlib

open scoped Nat
open scoped Real

/--
What is the product of the real roots of the equation \[x^2 + 18x + 30 = 2 \sqrt{x^2 + 18x + 45}\,\,?\] -/
theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (h₁ : Fintype (f ⁻¹' {0})) : ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by
  set r1 := -9 + Real.sqrt 61 with hr1_def
  set r2 := -9 - Real.sqrt 61 with hr2_def
  have h_sum : r1 + r2 = -18 := by
    dsimp [r1, r2]
    ring
  have h_prod : r1 * r2 = 20 := by
    dsimp [r1, r2]
    ring
    norm_num
  have h_factor : ∀ x : ℝ, x ^ 2 + 18 * x + 20 = (x - r1) * (x - r2) := by
    intro x
    calc
      x ^ 2 + 18 * x + 20 = x ^ 2 - (r1 + r2) * x + (r1 * r2) := by rw [h_sum, h_prod]; ring
      _ = (x - r1) * (x - r2) := by ring
  have h_eq : ∀ x, f x = 0 ↔ x ^ 2 + 18 * x + 20 = 0 := by
    intro x
    constructor
    · intro hf
      rw [h₀ x] at hf
      have htemp : x ^ 2 + 18 * x + 30 = 2 * Real.sqrt (x ^ 2 + 18 * x + 45) := by
        grind
      have hA_nonneg : 0 ≤ x ^ 2 + 18 * x + 30 := by
        rw [htemp]
        have hsqrt_nonneg : 0 ≤ Real.sqrt (x ^ 2 + 18 * x + 45) := Real.sqrt_nonneg _
        have h2 : (0:ℝ) ≤ 2 := by norm_num
        exact mul_nonneg h2 hsqrt_nonneg
      have hB_nonneg : 0 ≤ x ^ 2 + 18 * x + 45 := by
        by_contra hB_neg
        have hB_neg' : x ^ 2 + 18 * x + 45 < 0 := by linarith
        have hsqrt_zero : Real.sqrt (x ^ 2 + 18 * x + 45) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (by linarith)
        rw [hsqrt_zero] at htemp
        have hA_zero : x ^ 2 + 18 * x + 30 = 0 := by linarith
        nlinarith
      have h_sq : (x ^ 2 + 18 * x + 30)^2 = 4 * (x ^ 2 + 18 * x + 45) := by
        rw [htemp]
        have h_sqrt_sq : (Real.sqrt (x ^ 2 + 18 * x + 45))^2 = x ^ 2 + 18 * x + 45 :=
          Real.sq_sqrt hB_nonneg
        calc
          (2 * Real.sqrt (x ^ 2 + 18 * x + 45))^2 = 4 * ((Real.sqrt (x ^ 2 + 18 * x + 45))^2) := by ring
          _ = 4 * (x ^ 2 + 18 * x + 45) := by rw [h_sqrt_sq]
      have hA_eq : x ^ 2 + 18 * x + 30 = 10 := by
        have h_rhs : 4 * (x ^ 2 + 18 * x + 45) = 4 * (x ^ 2 + 18 * x + 30) + 60 := by ring
        rw [h_rhs] at h_sq
        nlinarith
      nlinarith
    · intro h_quad
      rw [h₀ x]
      have hx2 : x ^ 2 + 18 * x = -20 := by nlinarith
      have hA : x ^ 2 + 18 * x + 30 = 10 := by nlinarith
      have hB : x ^ 2 + 18 * x + 45 = 25 := by nlinarith
      have hsqrt : Real.sqrt (x ^ 2 + 18 * x + 45) = 5 := by
        rw [hB]
        norm_num
      grind
  have h_finset : (f ⁻¹' {0}).toFinset = {r1, r2} := by
    ext x
    constructor
    · intro hx
      grind
    · intro hx
      aesop
  have h_ne : r1 ≠ r2 := by
    intro h_eq_r
    have h_sqrt_zero : Real.sqrt 61 = 0 := by linarith
    have h61pos : Real.sqrt 61 > 0 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 61)
    linarith
  have h_not_mem : r1 ∉ ({r2} : Finset ℝ) := by
    intro h
    apply h_ne
    exact Finset.mem_singleton.mp h
  calc
    ∏ x ∈ (f ⁻¹' {0}).toFinset, x = ∏ x ∈ ({r1, r2} : Finset ℝ), x := by rw [h_finset]
    _ = r1 * r2 := by
      rw [Finset.prod_insert h_not_mem, Finset.prod_singleton]
    _ = 20 := by rw [h_prod]
