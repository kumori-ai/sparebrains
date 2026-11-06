import Mathlib

open scoped Nat
open scoped Real

/--
Two different positive numbers $ a$ and $ b$ each differ from their reciprocals by 1. What is $ a +{} b$?
\[ \textbf{(A) } 1 \qquad \textbf{(B) } 2 \qquad \textbf{(C) } \sqrt {5} \qquad \textbf{(D) } \sqrt {6} \qquad \textbf{(E) } 3
\] -/
theorem amc12a_2002_p13 (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ≠ b) (h₂ : abs (a - 1 / a) = 1)
    (h₃ : abs (b - 1 / b) = 1) : a + b = Real.sqrt 5 := by
  rcases h₀ with ⟨ha_pos, hb_pos⟩
  have ha_ne_zero : a ≠ 0 := by linarith
  have hb_ne_zero : b ≠ 0 := by linarith
  have h₂sq : (a - 1 / a)^2 = 1 := by
    have := congrArg (fun x => x ^ 2) h₂
    simpa [sq_abs] using this
  have h₃sq : (b - 1 / b)^2 = 1 := by
    have := congrArg (fun x => x ^ 2) h₃
    simpa [sq_abs] using this
  have ha_factor : (a^2 - a - 1) * (a^2 + a - 1) = 0 := by
    have htemp : a^4 - 3*a^2 + 1 = 0 := by
      field_simp [ha_ne_zero] at h₂sq
      nlinarith
    have factor_eq : (a^2 - a - 1) * (a^2 + a - 1) = a^4 - 3*a^2 + 1 := by ring
    rw [factor_eq, htemp]
  have hb_factor : (b^2 - b - 1) * (b^2 + b - 1) = 0 := by
    have htemp : b^4 - 3*b^2 + 1 = 0 := by
      field_simp [hb_ne_zero] at h₃sq
      nlinarith
    have factor_eq : (b^2 - b - 1) * (b^2 + b - 1) = b^4 - 3*b^2 + 1 := by ring
    rw [factor_eq, htemp]
  have ha_cases := eq_zero_or_eq_zero_of_mul_eq_zero ha_factor
  have hb_cases := eq_zero_or_eq_zero_of_mul_eq_zero hb_factor
  have h_solve_minus (x : ℝ) (hxpos : 0 < x) (hx : x^2 - x - 1 = 0) : x = (1 + Real.sqrt 5)/2 := by
    have hx_gt_one : 1 < x := by
      by_contra! hle
      have h_nonpos : x^2 - x - 1 ≤ -1 := by nlinarith
      nlinarith
    have h_pos : 0 ≤ 2*x - 1 := by nlinarith
    have h_sq : (2*x - 1)^2 = 5 := by nlinarith
    have h_sqrt : 2*x - 1 = Real.sqrt 5 := by
      calc
        2*x - 1 = Real.sqrt ((2*x - 1)^2) := by rw [Real.sqrt_sq h_pos]
        _ = Real.sqrt 5 := by rw [h_sq]
    nlinarith
  have h_solve_plus (x : ℝ) (hxpos : 0 < x) (hx : x^2 + x - 1 = 0) : x = (-1 + Real.sqrt 5)/2 := by
    have h_pos : 0 ≤ 2*x + 1 := by nlinarith
    have h_sq : (2*x + 1)^2 = 5 := by nlinarith
    have h_sqrt : 2*x + 1 = Real.sqrt 5 := by
      calc
        2*x + 1 = Real.sqrt ((2*x + 1)^2) := by rw [Real.sqrt_sq h_pos]
        _ = Real.sqrt 5 := by rw [h_sq]
    nlinarith
  rcases ha_cases with (ha_minus | ha_plus)
  · -- ha_minus: a^2 - a - 1 = 0
    have ha_eq_val : a = (1 + Real.sqrt 5)/2 := h_solve_minus a ha_pos ha_minus
    rcases hb_cases with (hb_minus | hb_plus)
    · -- both minus, contradiction
      have hb_eq_val : b = (1 + Real.sqrt 5)/2 := h_solve_minus b hb_pos hb_minus
      exfalso; exact h₁ (ha_eq_val.trans hb_eq_val.symm)
    · -- hb_plus: b^2 + b - 1 = 0
      have hb_eq_val : b = (-1 + Real.sqrt 5)/2 := h_solve_plus b hb_pos hb_plus
      calc
        a + b = ((1 + Real.sqrt 5)/2) + ((-1 + Real.sqrt 5)/2) := by rw [ha_eq_val, hb_eq_val]
        _ = Real.sqrt 5 := by ring
  · -- ha_plus: a^2 + a - 1 = 0
    have ha_eq_val : a = (-1 + Real.sqrt 5)/2 := h_solve_plus a ha_pos ha_plus
    rcases hb_cases with (hb_minus | hb_plus)
    · -- hb_minus
      have hb_eq_val : b = (1 + Real.sqrt 5)/2 := h_solve_minus b hb_pos hb_minus
      calc
        a + b = ((-1 + Real.sqrt 5)/2) + ((1 + Real.sqrt 5)/2) := by rw [ha_eq_val, hb_eq_val]
        _ = Real.sqrt 5 := by ring
    · -- both plus, contradiction
      have hb_eq_val : b = (-1 + Real.sqrt 5)/2 := h_solve_plus b hb_pos hb_plus
      exfalso; exact h₁ (ha_eq_val.trans hb_eq_val.symm)
