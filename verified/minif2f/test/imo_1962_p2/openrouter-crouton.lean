import Mathlib

open scoped Nat
open scoped Real

/--
Determine all real numbers $x$ which satisfy the inequality: \[ \sqrt{3-x}-\sqrt{x+1}>\dfrac{1}{2} \] -/
theorem imo_1962_p2 :
    {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)} =
      Set.Ico (-1) (1 - Real.sqrt 31 / 8) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  have hs31 : (Real.sqrt 31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
  have hs31nn : 0 ≤ Real.sqrt 31 := Real.sqrt_nonneg 31
  have hr2 : (7 : ℝ) / 8 < 1 + Real.sqrt 31 / 8 := by linarith
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    have ha : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg _
    have hb : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
    have hpos : 0 < (Real.sqrt (3 - x) - (1 / 2 + Real.sqrt (x + 1))) *
        (Real.sqrt (3 - x) + (1 / 2 + Real.sqrt (x + 1))) :=
      mul_pos (by linarith) (by linarith)
    have hsq1 : (1 / 2 + Real.sqrt (x + 1)) ^ 2 < (Real.sqrt (3 - x)) ^ 2 := by
      nlinarith [hpos, Real.sq_sqrt h1, Real.sq_sqrt h2]
    rw [Real.sq_sqrt h1] at hsq1
    have hb_lt : Real.sqrt (x + 1) < 7 / 4 - 2 * x := by
      nlinarith [hsq1, Real.sq_sqrt h2]
    have hx7 : x < 7 / 8 := by linarith
    have hpos2 : 0 < ((7 / 4 - 2 * x) - Real.sqrt (x + 1)) *
        ((7 / 4 - 2 * x) + Real.sqrt (x + 1)) :=
      mul_pos (by linarith) (by linarith)
    have hsq2 : (Real.sqrt (x + 1)) ^ 2 < (7 / 4 - 2 * x) ^ 2 := by
      nlinarith [hpos2]
    rw [Real.sq_sqrt h2] at hsq2
    have hpoly : 0 < 4 * x ^ 2 - 8 * x + 33 / 16 := by nlinarith [hsq2]
    refine ⟨by linarith, ?_⟩
    by_contra hnot
    push_neg at hnot
    have hprod : 0 ≤ (x - (1 - Real.sqrt 31 / 8)) * ((1 + Real.sqrt 31 / 8) - x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod, hpoly, hs31, hs31nn]
  · intro h
    obtain ⟨hge, hlt⟩ := h
    have h1le : (1 : ℝ) ≤ Real.sqrt 31 := by
      have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 31 by norm_num)
      rwa [Real.sqrt_one] at hh
    have hx7 : x < 7 / 8 := by linarith
    have hprod : 0 < ((1 - Real.sqrt 31 / 8) - x) * ((1 + Real.sqrt 31 / 8) - x) :=
      mul_pos (by linarith) (by linarith)
    have hsq : x + 1 < (7 / 4 - 2 * x) ^ 2 := by nlinarith [hprod, hs31]
    have hb_lt : Real.sqrt (x + 1) < 7 / 4 - 2 * x := by
      have hh := Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ x + 1) hsq
      rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 7 / 4 - 2 * x)] at hh
    have hsq2 : (1 / 2 + Real.sqrt (x + 1)) ^ 2 < 3 - x := by
      nlinarith [hb_lt, Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith)]
    have hlt2 : 1 / 2 + Real.sqrt (x + 1) < Real.sqrt (3 - x) := by
      have hh := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ (1 / 2 + Real.sqrt (x + 1)) ^ 2) hsq2
      rwa [Real.sqrt_sq (by have := Real.sqrt_nonneg (x + 1); linarith : (0 : ℝ) ≤ 1 / 2 + Real.sqrt (x + 1))] at hh
    refine ⟨by linarith, by linarith, by linarith⟩
