import Mathlib

open scoped Nat
open scoped Real

/--
For what values of the variable $x$ does the following inequality hold: \[ \dfrac{4x^2}{(1-\sqrt{2x+1})^2}< 2x+9 \ ?  \] -/
theorem imo_1960_p2 :
    { x : ℝ |
      0 ≤ 1 + 2 * x ∧ (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 ∧
      4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 } = Set.Ico (-(1 / 2)) (45 / 8) \ {0} := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    set t := Real.sqrt (1 + 2 * x) with ht_def
    have h2t : (1 - t) ^ 2 ≠ 0 := by simpa [ht_def] using h2
    have h3t : 4 * x ^ 2 / (1 - t) ^ 2 < 2 * x + 9 := by simpa [ht_def] using h3
    have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = 1 + 2 * x := Real.sq_sqrt h1
    have ht_ne : t ≠ 1 := by
      intro hte
      apply h2t
      rw [hte]
      norm_num
    have hden : (1 - t) ≠ 0 := by
      intro h
      apply ht_ne
      linarith
    have hden2 : (1 - t) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    have h4 : 4 * x ^ 2 = (t + 1) ^ 2 * (1 - t) ^ 2 := by
      have hx : 2 * x = t ^ 2 - 1 := by linarith [ht_sq]
      calc 4 * x ^ 2 = (2 * x) ^ 2 := by ring
        _ = (t ^ 2 - 1) ^ 2 := by rw [hx]
        _ = (t + 1) ^ 2 * (1 - t) ^ 2 := by ring
    have hfrac : 4 * x ^ 2 / (1 - t) ^ 2 = (t + 1) ^ 2 := by
      rw [h4]
      field_simp [hden2]
    rw [hfrac] at h3t
    have ht_lt : t < 7 / 2 := by
      have hexp : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
      rw [hexp] at h3t
      linarith [ht_sq, h3t]
    have hx_lt : x < 45 / 8 := by
      have hprod : 0 < (7 / 2 - t) * (7 / 2 + t) :=
        mul_pos (by linarith) (by linarith)
      have htsq_lt : t ^ 2 < (7 / 2) ^ 2 := by nlinarith [hprod]
      have hnum : (7 / 2 : ℝ) ^ 2 = 49 / 4 := by norm_num
      linarith [ht_sq, htsq_lt, hnum]
    have hx_ne : x ≠ 0 := by
      intro hx0
      apply ht_ne
      rw [ht_def, hx0]
      norm_num
    exact ⟨⟨by linarith [h1], hx_lt⟩, by simp [hx_ne]⟩
  · rintro ⟨⟨hlow, hhigh⟩, hxnot⟩
    have hx_ne : x ≠ 0 := by
      intro h
      apply hxnot
      simp [h]
    have h1 : 0 ≤ 1 + 2 * x := by linarith [hlow]
    set t := Real.sqrt (1 + 2 * x) with ht_def
    have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = 1 + 2 * x := Real.sq_sqrt h1
    have ht_ne : t ≠ 1 := by
      intro hte
      apply hx_ne
      have htsq1 : t ^ 2 = 1 := by rw [hte]; norm_num
      linarith [ht_sq, htsq1]
    have hden : (1 - t) ≠ 0 := by
      intro h
      apply ht_ne
      linarith
    have hden2 : (1 - t) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    have h4 : 4 * x ^ 2 = (t + 1) ^ 2 * (1 - t) ^ 2 := by
      have hx : 2 * x = t ^ 2 - 1 := by linarith [ht_sq]
      calc 4 * x ^ 2 = (2 * x) ^ 2 := by ring
        _ = (t ^ 2 - 1) ^ 2 := by rw [hx]
        _ = (t + 1) ^ 2 * (1 - t) ^ 2 := by ring
    have hfrac : 4 * x ^ 2 / (1 - t) ^ 2 = (t + 1) ^ 2 := by
      rw [h4]
      field_simp [hden2]
    have ht_lt : t < 7 / 2 := by
      have htsq_lt : t ^ 2 < 49 / 4 := by
        rw [ht_sq]
        linarith [hhigh]
      by_contra h
      push_neg at h
      have hprod : 0 ≤ (t - 7 / 2) * (t + 7 / 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod, htsq_lt]
    have hineq : 4 * x ^ 2 / (1 - t) ^ 2 < 2 * x + 9 := by
      rw [hfrac]
      have hexp : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
      rw [hexp]
      linarith [ht_sq, ht_lt]
    refine ⟨h1, ?_, ?_⟩
    · simpa [ht_def] using hden2
    · simpa [ht_def] using hineq
