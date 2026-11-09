import Mathlib

open scoped Nat
open scoped Real

/--
What is the product of the real roots of the equation \[x^2 + 18x + 30 = 2 \sqrt{x^2 + 18x + 45}\,\,?\] -/
theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (h₁ : Fintype (f ⁻¹' {0})) : ∏ x ∈ (f ⁻¹' {0}).toFinset, x = 20 := by
  set a := -9 + Real.sqrt 61 with ha
  set b := -9 - Real.sqrt 61 with hb
  have h61 : (Real.sqrt 61) ^ 2 = 61 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 61 := Real.sqrt_pos.mpr (by norm_num)
  have hab_ne : a ≠ b := by
    rw [ha, hb]
    intro h
    have h0 : Real.sqrt 61 = 0 := by linarith
    linarith
  have hab_sum : a + b = -18 := by
    rw [ha, hb]; ring
  have hab_prod : a * b = 20 := by
    rw [ha, hb]
    have h : (-9 + Real.sqrt 61) * (-9 - Real.sqrt 61) = 81 - (Real.sqrt 61) ^ 2 := by ring
    rw [h, h61]; norm_num
  have key : ∀ x, f x = 0 ↔ x ^ 2 + 18 * x + 20 = 0 := by
    intro x
    constructor
    · intro hx
      rw [h₀ x] at hx
      set t := x ^ 2 + (18 * x + 45) with ht
      have ht_nonneg : 0 ≤ t := by
        by_contra hneg
        push_neg at hneg
        have hsqrt0 : Real.sqrt t = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
        rw [hsqrt0] at hx
        have ht15 : t = 15 := by
          have h1 : t = (x ^ 2 + (18 * x + 30)) + 15 := by rw [ht]; ring
          linarith
        linarith
      have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht_nonneg
      have ht15 : t - 15 = 2 * Real.sqrt t := by
        have h1 : t = (x ^ 2 + (18 * x + 30)) + 15 := by rw [ht]; ring
        linarith
      set u := Real.sqrt t with hu
      have hu_nonneg : 0 ≤ u := Real.sqrt_nonneg t
      have hu_sq : u ^ 2 = t := hsqrt_sq
      have hquad : u ^ 2 - 2 * u - 15 = 0 := by linarith
      have hfactor : (u - 5) * (u + 3) = 0 := by
        have h : (u - 5) * (u + 3) = u ^ 2 - 2 * u - 15 := by ring
        rw [h]; exact hquad
      have hu5 : u = 5 := by
        rcases mul_eq_zero.mp hfactor with h | h
        · linarith
        · linarith
      have ht25 : t = 25 := by
        rw [← hu_sq, hu5]; norm_num
      have h1 : t = x ^ 2 + (18 * x + 45) := ht
      linarith
    · intro hx
      rw [h₀ x]
      have ht25 : x ^ 2 + (18 * x + 45) = 25 := by linarith
      have hsqrt : Real.sqrt (x ^ 2 + (18 * x + 45)) = 5 := by
        rw [ht25]
        have h : (25 : ℝ) = 5 ^ 2 := by norm_num
        rw [h]
        exact Real.sqrt_sq (by norm_num)
      rw [hsqrt]
      linarith
  have hset : f ⁻¹' {0} = {a, b} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
    rw [key x]
    constructor
    · intro hx
      have hfactor : (x - a) * (x - b) = 0 := by
        have h : (x - a) * (x - b) = x ^ 2 + 18 * x + 20 := by
          calc (x - a) * (x - b) = x ^ 2 - (a + b) * x + a * b := by ring
            _ = x ^ 2 + 18 * x + 20 := by rw [hab_sum, hab_prod]; ring
        rw [h]; exact hx
      rcases mul_eq_zero.mp hfactor with h | h
      · left; linarith
      · right; linarith
    · intro hx
      rcases hx with rfl | rfl
      · rw [ha]
        have h : (-9 + Real.sqrt 61) ^ 2 + 18 * (-9 + Real.sqrt 61) + 20
            = (Real.sqrt 61) ^ 2 - 61 := by ring
        rw [h, h61]; norm_num
      · rw [hb]
        have h : (-9 - Real.sqrt 61) ^ 2 + 18 * (-9 - Real.sqrt 61) + 20
            = (Real.sqrt 61) ^ 2 - 61 := by ring
        rw [h, h61]; norm_num
  have hfinset : (f ⁻¹' {0}).toFinset = {a, b} := by
    ext x
    simp only [Set.mem_toFinset]
    rw [hset]
    simp
  rw [hfinset, Finset.prod_pair hab_ne]
  exact hab_prod
