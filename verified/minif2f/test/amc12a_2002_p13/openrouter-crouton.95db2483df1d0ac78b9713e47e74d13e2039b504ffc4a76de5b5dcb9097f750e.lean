import Mathlib

open scoped Nat
open scoped Real

/--
Two different positive numbers $ a$ and $ b$ each differ from their reciprocals by 1. What is $ a +{} b$?
\[ \textbf{(A) } 1 \qquad \textbf{(B) } 2 \qquad \textbf{(C) } \sqrt {5} \qquad \textbf{(D) } \sqrt {6} \qquad \textbf{(E) } 3
\] -/
theorem amc12a_2002_p13 (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ≠ b) (h₂ : abs (a - 1 / a) = 1)
    (h₃ : abs (b - 1 / b) = 1) : a + b = Real.sqrt 5 := by
  obtain ⟨ha_pos, hb_pos⟩ := h₀
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have uniq : ∀ x y : ℝ, 0 < x → 0 < y → x - 1 / x = y - 1 / y → x = y := by
    intro x y hx hy h
    have hxne : x ≠ 0 := ne_of_gt hx
    have hyne : y ≠ 0 := ne_of_gt hy
    have h3 : x - y = 1 / x - 1 / y := by linarith
    have h5 : (x - y) * (x * y) = y - x := by
      calc (x - y) * (x * y) = (1 / x - 1 / y) * (x * y) := by rw [← h3]
        _ = y - x := by field_simp
    have h6 : (x - y) * (x * y + 1) = 0 := by
      have hexp : (x - y) * (x * y + 1) = (x - y) * (x * y) + (x - y) := by ring
      rw [hexp, h5]; ring
    rcases mul_eq_zero.mp h6 with h7 | h7
    · linarith
    · have hxy : 0 < x * y := mul_pos hx hy
      linarith
  have ha_cases : a - 1 / a = 1 ∨ a - 1 / a = -1 := eq_or_eq_neg_of_abs_eq h₂
  have hb_cases : b - 1 / b = 1 ∨ b - 1 / b = -1 := eq_or_eq_neg_of_abs_eq h₃
  rcases ha_cases with ha | ha <;> rcases hb_cases with hb | hb
  · exfalso
    exact h₁ (uniq a b ha_pos hb_pos (by rw [ha, hb]))
  · have hb_eq : b = 1 / a := by
      apply uniq b (1 / a) hb_pos (one_div_pos.mpr ha_pos)
      have hval : (1 / a) - 1 / (1 / a) = -1 := by
        rw [one_div_one_div a]
        linarith
      rw [hval, hb]
    have hsum : a + b = a + 1 / a := by rw [hb_eq]
    have hsq : (a + b) ^ 2 = 5 := by
      rw [hsum]
      have hexp : (a + 1 / a) ^ 2 = (a - 1 / a) ^ 2 + 4 := by
        field_simp
        ring
      rw [hexp, ha]
      norm_num
    have hpos_sum : 0 < a + b := add_pos ha_pos hb_pos
    calc a + b = Real.sqrt ((a + b) ^ 2) := (Real.sqrt_sq hpos_sum.le).symm
      _ = Real.sqrt 5 := by rw [hsq]
  · have ha_eq : a = 1 / b := by
      apply uniq a (1 / b) ha_pos (one_div_pos.mpr hb_pos)
      have hval : (1 / b) - 1 / (1 / b) = -1 := by
        rw [one_div_one_div b]
        linarith
      rw [hval, ha]
    have hsum : a + b = b + 1 / b := by rw [ha_eq]; ring
    have hsq : (a + b) ^ 2 = 5 := by
      rw [hsum]
      have hexp : (b + 1 / b) ^ 2 = (b - 1 / b) ^ 2 + 4 := by
        field_simp
        ring
      rw [hexp, hb]
      norm_num
    have hpos_sum : 0 < a + b := add_pos ha_pos hb_pos
    calc a + b = Real.sqrt ((a + b) ^ 2) := (Real.sqrt_sq hpos_sum.le).symm
      _ = Real.sqrt 5 := by rw [hsq]
  · exfalso
    exact h₁ (uniq a b ha_pos hb_pos (by rw [ha, hb]))
