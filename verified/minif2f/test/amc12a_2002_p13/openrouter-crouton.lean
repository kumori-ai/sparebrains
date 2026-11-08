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
  have key1 : ∀ x : ℝ, 0 < x → x - 1 / x = 1 → x ^ 2 = x + 1 := by
    intro x hx h
    have hxne : x ≠ 0 := ne_of_gt hx
    have hmul : x * (x - 1 / x) = x ^ 2 - 1 := by
      rw [mul_sub, one_div, mul_inv_cancel₀ hxne]
      ring
    rw [h] at hmul
    have hxeq : x = x ^ 2 - 1 := by simpa using hmul
    linarith
  have key2 : ∀ x : ℝ, 0 < x → x - 1 / x = -1 → x ^ 2 = -x + 1 := by
    intro x hx h
    have hxne : x ≠ 0 := ne_of_gt hx
    have hmul : x * (x - 1 / x) = x ^ 2 - 1 := by
      rw [mul_sub, one_div, mul_inv_cancel₀ hxne]
      ring
    rw [h] at hmul
    have hxeq : -x = x ^ 2 - 1 := by simpa using hmul
    linarith
  have finish : (a + b) ^ 2 = 5 → a + b = Real.sqrt 5 := by
    intro h
    have hpos : 0 ≤ a + b := by linarith
    calc a + b = Real.sqrt ((a + b) ^ 2) := (Real.sqrt_sq hpos).symm
      _ = Real.sqrt 5 := by rw [h]
  have ha_cases : a - 1 / a = 1 ∨ a - 1 / a = -1 := eq_or_eq_neg_of_abs_eq h₂
  have hb_cases : b - 1 / b = 1 ∨ b - 1 / b = -1 := eq_or_eq_neg_of_abs_eq h₃
  rcases ha_cases with ha1 | ha1
  · rcases hb_cases with hb1 | hb1
    · -- both +1, impossible since a ≠ b
      have ha_sq := key1 a ha_pos ha1
      have hb_sq := key1 b hb_pos hb1
      have hprod : (a - b) * (a + b - 1) = 0 := by linear_combination ha_sq - hb_sq
      rcases mul_eq_zero.mp hprod with h | h
      · exfalso
        apply h₁
        linarith
      · exfalso
        have hab1 : a + b = 1 := by linarith
        have hpos : 0 < a * (1 - a) := mul_pos ha_pos (by linarith)
        nlinarith [ha_sq, hpos]
    · -- a is +, b is -
      have ha_sq := key1 a ha_pos ha1
      have hb_sq := key2 b hb_pos hb1
      have hprod : (a + b) * (a - b - 1) = 0 := by linear_combination ha_sq - hb_sq
      have hdiff : a - b = 1 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exfalso
          linarith
        · linarith
      have hab : a * b = 1 := by
        have hbeq : b = a - 1 := by linarith
        rw [hbeq]
        linear_combination ha_sq
      have hsq5 : (a + b) ^ 2 = 5 := by
        linear_combination ha_sq + hb_sq + 2 * hab + hdiff
      exact finish hsq5
  · rcases hb_cases with hb1 | hb1
    · -- a is -, b is +
      have ha_sq := key2 a ha_pos ha1
      have hb_sq := key1 b hb_pos hb1
      have hprod : (a + b) * (b - a - 1) = 0 := by linear_combination hb_sq - ha_sq
      have hdiff : b - a = 1 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exfalso
          linarith
        · linarith
      have hab : a * b = 1 := by
        have haeq : a = b - 1 := by linarith
        rw [haeq]
        linear_combination hb_sq
      have hsq5 : (a + b) ^ 2 = 5 := by
        linear_combination ha_sq + hb_sq + 2 * hab + hdiff
      exact finish hsq5
    · -- both -1, impossible since a,b > 0
      have ha_sq := key2 a ha_pos ha1
      have hb_sq := key2 b hb_pos hb1
      have hprod : (a - b) * (a + b + 1) = 0 := by linear_combination ha_sq - hb_sq
      rcases mul_eq_zero.mp hprod with h | h
      · exfalso
        apply h₁
        linarith
      · exfalso
        linarith
