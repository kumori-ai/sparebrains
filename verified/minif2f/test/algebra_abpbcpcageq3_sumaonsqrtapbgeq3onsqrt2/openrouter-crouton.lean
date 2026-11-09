import Mathlib

open scoped Nat
open scoped Real

theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 3 ≤ a * b + b * c + c * a) :
    3 / Real.sqrt 2 ≤ a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have hab : 0 < a + b := by linarith
  have hbc : 0 < b + c := by linarith
  have hca : 0 < c + a := by linarith
  have hp : 0 < a + b + c := by linarith
  have hSpos : 0 < a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) := by
    apply add_pos
    · apply add_pos
      · exact div_pos ha (Real.sqrt_pos.mpr hab)
      · exact div_pos hb (Real.sqrt_pos.mpr hbc)
    · exact div_pos hc (Real.sqrt_pos.mpr hca)
  have hTpos : 0 < a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a) := by
    apply add_pos
    · apply add_pos
      · exact mul_pos ha (Real.sqrt_pos.mpr hab)
      · exact mul_pos hb (Real.sqrt_pos.mpr hbc)
    · exact mul_pos hc (Real.sqrt_pos.mpr hca)
  have hDpos : 0 < a * (a + b) + b * (b + c) + c * (c + a) := by
    apply add_pos
    · apply add_pos
      · exact mul_pos ha hab
      · exact mul_pos hb hbc
    · exact mul_pos hc hca
  have cauchy3 : ∀ x1 x2 x3 y1 y2 y3 : ℝ,
      (x1 * y1 + x2 * y2 + x3 * y3) ^ 2 ≤
        (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by
    intro x1 x2 x3 y1 y2 y3
    nlinarith [sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 * y3 - x3 * y1),
      sq_nonneg (x2 * y3 - x3 * y2)]
  have hprod1 : Real.sqrt (a / Real.sqrt (a + b)) * Real.sqrt (a * Real.sqrt (a + b)) = a := by
    rw [← Real.sqrt_mul (div_nonneg ha.le (Real.sqrt_nonneg _))]
    have hne : Real.sqrt (a + b) ≠ 0 := Real.sqrt_ne_zero'.mpr hab
    have he : a / Real.sqrt (a + b) * (a * Real.sqrt (a + b)) = a ^ 2 := by
      field_simp
    rw [he, Real.sqrt_sq ha.le]
  have hprod2 : Real.sqrt (b / Real.sqrt (b + c)) * Real.sqrt (b * Real.sqrt (b + c)) = b := by
    rw [← Real.sqrt_mul (div_nonneg hb.le (Real.sqrt_nonneg _))]
    have hne : Real.sqrt (b + c) ≠ 0 := Real.sqrt_ne_zero'.mpr hbc
    have he : b / Real.sqrt (b + c) * (b * Real.sqrt (b + c)) = b ^ 2 := by
      field_simp
    rw [he, Real.sqrt_sq hb.le]
  have hprod3 : Real.sqrt (c / Real.sqrt (c + a)) * Real.sqrt (c * Real.sqrt (c + a)) = c := by
    rw [← Real.sqrt_mul (div_nonneg hc.le (Real.sqrt_nonneg _))]
    have hne : Real.sqrt (c + a) ≠ 0 := Real.sqrt_ne_zero'.mpr hca
    have he : c / Real.sqrt (c + a) * (c * Real.sqrt (c + a)) = c ^ 2 := by
      field_simp
    rw [he, Real.sqrt_sq hc.le]
  have hsq1a : (Real.sqrt (a / Real.sqrt (a + b))) ^ 2 = a / Real.sqrt (a + b) :=
    Real.sq_sqrt (div_nonneg ha.le (Real.sqrt_nonneg _))
  have hsq1b : (Real.sqrt (a * Real.sqrt (a + b))) ^ 2 = a * Real.sqrt (a + b) :=
    Real.sq_sqrt (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hsq2a : (Real.sqrt (b / Real.sqrt (b + c))) ^ 2 = b / Real.sqrt (b + c) :=
    Real.sq_sqrt (div_nonneg hb.le (Real.sqrt_nonneg _))
  have hsq2b : (Real.sqrt (b * Real.sqrt (b + c))) ^ 2 = b * Real.sqrt (b + c) :=
    Real.sq_sqrt (mul_nonneg hb.le (Real.sqrt_nonneg _))
  have hsq3a : (Real.sqrt (c / Real.sqrt (c + a))) ^ 2 = c / Real.sqrt (c + a) :=
    Real.sq_sqrt (div_nonneg hc.le (Real.sqrt_nonneg _))
  have hsq3b : (Real.sqrt (c * Real.sqrt (c + a))) ^ 2 = c * Real.sqrt (c + a) :=
    Real.sq_sqrt (mul_nonneg hc.le (Real.sqrt_nonneg _))
  have hc1 := cauchy3 (Real.sqrt (a / Real.sqrt (a + b))) (Real.sqrt (b / Real.sqrt (b + c)))
    (Real.sqrt (c / Real.sqrt (c + a))) (Real.sqrt (a * Real.sqrt (a + b)))
    (Real.sqrt (b * Real.sqrt (b + c))) (Real.sqrt (c * Real.sqrt (c + a)))
  rw [hprod1, hprod2, hprod3, hsq1a, hsq2a, hsq3a, hsq1b, hsq2b, hsq3b] at hc1
  have hprod1' : Real.sqrt a * Real.sqrt (a * (a + b)) = a * Real.sqrt (a + b) := by
    rw [← Real.sqrt_mul ha.le]
    have he : a * (a * (a + b)) = a ^ 2 * (a + b) := by ring
    rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  have hprod2' : Real.sqrt b * Real.sqrt (b * (b + c)) = b * Real.sqrt (b + c) := by
    rw [← Real.sqrt_mul hb.le]
    have he : b * (b * (b + c)) = b ^ 2 * (b + c) := by ring
    rw [he, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  have hprod3' : Real.sqrt c * Real.sqrt (c * (c + a)) = c * Real.sqrt (c + a) := by
    rw [← Real.sqrt_mul hc.le]
    have he : c * (c * (c + a)) = c ^ 2 * (c + a) := by ring
    rw [he, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hsq1a' : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hsq1b' : (Real.sqrt (a * (a + b))) ^ 2 = a * (a + b) :=
    Real.sq_sqrt (mul_nonneg ha.le hab.le)
  have hsq2a' : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hsq2b' : (Real.sqrt (b * (b + c))) ^ 2 = b * (b + c) :=
    Real.sq_sqrt (mul_nonneg hb.le hbc.le)
  have hsq3a' : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  have hsq3b' : (Real.sqrt (c * (c + a))) ^ 2 = c * (c + a) :=
    Real.sq_sqrt (mul_nonneg hc.le hca.le)
  have hc2 := cauchy3 (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)
    (Real.sqrt (a * (a + b))) (Real.sqrt (b * (b + c))) (Real.sqrt (c * (c + a)))
  rw [hprod1', hprod2', hprod3', hsq1a', hsq2a', hsq3a', hsq1b', hsq2b', hsq3b'] at hc2
  have step1 : (a + b + c) ^ 2 * (a + b + c) ^ 2 ≤
      (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) *
      ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))) :=
    mul_le_mul hc1 hc1 (by positivity) (mul_nonneg hSpos.le hTpos.le)
  have step2 : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) *
      ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))) ≤
      (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
        ((a + b + c) * (a * (a + b) + b * (b + c) + c * (c + a))) := by
    have he : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) *
      ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))) =
      (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
  have h4 : (a + b + c) ^ 3 * (a + b + c) ≤
      ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
        (a * (a + b) + b * (b + c) + c * (c + a))) * (a + b + c) := by
    calc (a + b + c) ^ 3 * (a + b + c) = (a + b + c) ^ 2 * (a + b + c) ^ 2 := by ring
      _ ≤ (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) *
      ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) *
        (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))) := step1
      _ ≤ (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
        ((a + b + c) * (a * (a + b) + b * (b + c) + c * (c + a))) := step2
      _ = ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
        (a * (a + b) + b * (b + c) + c * (c + a))) * (a + b + c) := by ring
  have h5 : (a + b + c) ^ 3 ≤
      (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
        (a * (a + b) + b * (b + c) + c * (c + a)) :=
    le_of_mul_le_mul_right h4 hp
  have hDle : 9 * (a * (a + b) + b * (b + c) + c * (c + a)) ≤ 2 * (a + b + c) ^ 3 := by
    have hfact : 2 * (a + b + c) ^ 3 - 9 * (a * (a + b) + b * (b + c) + c * (c + a)) =
        (a + b + c - 3) ^ 2 * (2 * (a + b + c) + 3) + 9 * ((a * b + b * c + c * a) - 3) := by ring
    have hnonneg : 0 ≤ (a + b + c - 3) ^ 2 * (2 * (a + b + c) + 3) +
        9 * ((a * b + b * c + c * a) - 3) :=
      add_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
    linarith
  have hS2 : 9 ≤ 2 * (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 := by
    have hle : 9 * (a * (a + b) + b * (b + c) + c * (c + a)) ≤
        (2 * (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2) *
          (a * (a + b) + b * (b + c) + c * (c + a)) := by
      have hle2 : 2 * (a + b + c) ^ 3 ≤
          2 * ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
            (a * (a + b) + b * (b + c) + c * (c + a))) := by linarith [h5]
      have he : 2 * ((a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2 *
            (a * (a + b) + b * (b + c) + c * (c + a))) =
          (2 * (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)) ^ 2) *
            (a * (a + b) + b * (b + c) + c * (c + a)) := by ring
      linarith [hDle, hle2, he]
    exact le_of_mul_le_mul_right hle hDpos
  set S := a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) with hSdef
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (3 : ℝ) ^ 2 ≤ (S * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc (3 : ℝ) ^ 2 = 9 := by norm_num
      _ ≤ 2 * S ^ 2 := hS2
      _ = S ^ 2 * 2 := by ring
  have habs := abs_le_of_sq_le_sq hsq (mul_nonneg hSpos.le hsqrt2pos.le)
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at habs
  rw [div_le_iff₀ hsqrt2pos]
  exact habs
