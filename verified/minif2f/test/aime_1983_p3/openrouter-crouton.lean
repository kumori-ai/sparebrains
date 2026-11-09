import Mathlib

open scoped Nat
open scoped Real

/--
What is the product of the real roots of the equation \[x^2 + 18x + 30 = 2 \sqrt{x^2 + 18x + 45}\,\,?\] -/
theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (h₁ : Fintype (f ⁻¹' {0})) : ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by
  have h61 : (Real.sqrt 61) ^ 2 = 61 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 61 := Real.sqrt_pos.mpr (by norm_num)
  have hne : (-9 + Real.sqrt 61) ≠ (-9 - Real.sqrt 61) := by
    intro h
    linarith
  have hset : f ⁻¹' {0} = {-9 + Real.sqrt 61, -9 - Real.sqrt 61} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · intro hx
      rw [h₀] at hx
      have h1 : x ^ 2 + 18 * x + 45 - 15 = 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) := by
        linarith
      have hs_nonneg : 0 ≤ Real.sqrt (x ^ 2 + (18 * x + 45)) := Real.sqrt_nonneg _
      have ht_ge : 15 ≤ x ^ 2 + 18 * x + 45 := by linarith
      have hs_sq : (Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 = x ^ 2 + (18 * x + 45) :=
        Real.sq_sqrt (by linarith)
      have hsq : (x ^ 2 + 18 * x + 45 - 15) ^ 2 = 4 * (x ^ 2 + 18 * x + 45) := by
        rw [h1]
        have h2 : (2 * Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2
            = 4 * (Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 := by ring
        rw [h2, hs_sq]
        ring
      have hfactor : (x ^ 2 + 18 * x + 45 - 25) * (x ^ 2 + 18 * x + 45 - 9) = 0 := by
        have hexp : (x ^ 2 + 18 * x + 45 - 25) * (x ^ 2 + 18 * x + 45 - 9)
            = (x ^ 2 + 18 * x + 45 - 15) ^ 2 - 4 * (x ^ 2 + 18 * x + 45) := by ring
        rw [hexp, hsq]
        ring
      rcases mul_eq_zero.mp hfactor with h | h
      · have ht25 : x ^ 2 + 18 * x + 45 = 25 := by linarith
        have hsq61 : (x + 9) ^ 2 = (Real.sqrt 61) ^ 2 := by
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61)]
          have hexp : (x + 9) ^ 2 = x ^ 2 + 18 * x + 81 := by ring
          rw [hexp]
          linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq61 with h | h
        · left
          linarith
        · right
          linarith
      · have ht9 : x ^ 2 + 18 * x + 45 = 9 := by linarith
        exfalso
        linarith
    · intro hx
      rcases hx with rfl | rfl
      · have harg : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45) = 25 := by
          have hexp : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)
              = (Real.sqrt 61) ^ 2 - 36 := by ring
          rw [hexp, h61]
          norm_num
        have hsqrt25 : Real.sqrt (25 : ℝ) = 5 := by
          rw [show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [h₀, harg, hsqrt25]
        linarith
      · have harg : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45) = 25 := by
          have hexp : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)
              = (Real.sqrt 61) ^ 2 - 36 := by ring
          rw [hexp, h61]
          norm_num
        have hsqrt25 : Real.sqrt (25 : ℝ) = 5 := by
          rw [show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [h₀, harg, hsqrt25]
        linarith
  have hfinset : (f ⁻¹' {0}).toFinset = {-9 + Real.sqrt 61, -9 - Real.sqrt 61} := by
    ext y
    simp [hset]
  rw [hfinset, Finset.prod_pair hne]
  have hexp : (-9 + Real.sqrt 61) * (-9 - Real.sqrt 61) = 81 - (Real.sqrt 61) ^ 2 := by ring
  rw [hexp, h61]
  norm_num
