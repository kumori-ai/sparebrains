import Mathlib

open scoped Nat
open scoped Real

/--
For what values of the variable $x$ does the following inequality hold: \[ \dfrac{4x^2}{(1-\sqrt{2x+1})^2}< 2x+9 \ ?  \] -/
theorem imo_1960_p2 :
    { x : ℝ |
      0 ≤ 1 + 2 * x ∧ (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 ∧
      4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 } = Set.Ico (-(1 / 2)) (45 / 8) \ {0} := by
  -- Define the auxiliary function to simplify the expression
  ext x
  constructor
  · intro h
    rcases h with ⟨h1, h2, h3⟩
    have hx_ge : -(1/2 : ℝ) ≤ x := by linarith
    have hx_ne_zero : x ≠ 0 := by
      intro hzero
      have hzero' : ((1 : ℝ) - √((1 : ℝ) + (2 : ℝ) * x)) ^ (2 : ℕ) = (0 : ℝ) := by
        simp [hzero]
      exact h2 hzero'
    have hx_lt : x < 45/8 := by
      set s := √(1 + 2*x) with hs_def
      have hs_sq : s^2 = 1 + 2*x := Real.sq_sqrt h1
      have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
      have h_denom_ne_zero : (1 - s)^2 ≠ 0 := by
        simpa [hs_def] using h2
      have h3_s : (4*x^2) / ((1 - s)^2) < 2*x + 9 := by
        simpa [hs_def] using h3
      have h_eq : (4*x^2) / ((1 - s)^2) = (s + 1)^2 := by
        field_simp [h_denom_ne_zero]
        grind
      have h_rhs : 2*x + 9 = s^2 + 8 := by
        nlinarith [hs_sq]
      have h_ineq : (s + 1)^2 < s^2 + 8 := by
        calc
          (s + 1)^2 = (4*x^2) / ((1 - s)^2) := by symm; exact h_eq
          _ < 2*x + 9 := h3_s
          _ = s^2 + 8 := h_rhs
      have hs_lt : s < 7/2 := by
        nlinarith
      have hs_sq_lt : s^2 < (7/2)^2 := by
        have hpos : 0 ≤ (7/2 : ℝ) := by norm_num
        nlinarith
      nlinarith [hs_sq, hs_sq_lt]
    have hx_mem : x ∈ Set.Ico (-(1/2 : ℝ)) (45/8 : ℝ) \ {(0 : ℝ)} := by
      refine ⟨⟨hx_ge, hx_lt⟩, ?_⟩
      simp [hx_ne_zero]
    exact hx_mem
  · intro h
    rcases h with ⟨hx_mem, hx_ne_zero⟩
    rcases hx_mem with ⟨hx_ge, hx_lt⟩
    have h1 : 0 ≤ 1 + 2*x := by linarith
    have h2 : ((1 : ℝ) - √((1 : ℝ) + (2 : ℝ) * x)) ^ (2 : ℕ) ≠ (0 : ℝ) := by
      intro hzero
      grind
    have h3 : (4 : ℝ) * x ^ (2 : ℕ) / ((1 : ℝ) - √((1 : ℝ) + (2 : ℝ) * x)) ^ (2 : ℕ) < (2 : ℝ) * x + (9 : ℝ) := by
      set s := √(1 + 2*x) with hs_def
      have hs_sq : s^2 = 1 + 2*x := Real.sq_sqrt h1
      have h_denom_ne_zero : (1 - s)^2 ≠ 0 := by
        intro hzero
        aesop
      have hs_lt : s < 7/2 := by
        have hpos : 0 < (7/2 : ℝ) := by norm_num
        have h_sq_lt : 1 + 2*x < (7/2)^2 := by
          nlinarith
        nlinarith
      have h_eq : (4*x^2) / ((1 - s)^2) = (s + 1)^2 := by
        field_simp [h_denom_ne_zero]
        grind
      have h_rhs : 2*x + 9 = s^2 + 8 := by
        nlinarith [hs_sq]
      have h_ineq : (s + 1)^2 < s^2 + 8 := by
        nlinarith
      calc
        (4 : ℝ) * x ^ (2 : ℕ) / ((1 : ℝ) - √((1 : ℝ) + (2 : ℝ) * x)) ^ (2 : ℕ) = (4*x^2) / ((1 - s)^2) := by simp [hs_def]
        _ = (s + 1)^2 := h_eq
        _ < s^2 + 8 := h_ineq
        _ = 2*x + 9 := by symm; exact h_rhs
    exact ⟨h1, h2, h3⟩