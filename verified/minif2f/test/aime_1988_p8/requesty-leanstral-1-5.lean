import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$, defined on the set of ordered pairs of positive integers, satisfies the following properties:
\begin{eqnarray*} f(x,x) &=& x, \\ f(x,y) &=& f(y,x), \quad \text{and} \\ (x + y) f(x,y) &=& yf(x,x + y). \end{eqnarray*}
Calculate $f(14,52)$. -/
theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by
  have h14pos : 0 < 14 := by norm_num
  have h52pos : 0 < 52 := by norm_num
  have h38pos : 0 < 38 := by norm_num
  have h24pos : 0 < 24 := by norm_num
  have h10pos : 0 < 10 := by norm_num
  have h4pos : 0 < 4 := by norm_num
  have h6pos : 0 < 6 := by norm_num
  have h2pos : 0 < 2 := by norm_num
  have h_eq1 : (52 : ℝ) * f 14 38 = (38 : ℝ) * f 14 52 := by
    have h := h₂ 14 38 ⟨h14pos, h38pos⟩
    norm_num at h
    exact h
  have h_eq2 : (38 : ℝ) * f 14 24 = (24 : ℝ) * f 14 38 := by
    have h := h₂ 14 24 ⟨h14pos, h24pos⟩
    norm_num at h
    exact h
  have h_eq3 : (24 : ℝ) * f 14 10 = (10 : ℝ) * f 14 24 := by
    have h := h₂ 14 10 ⟨h14pos, h10pos⟩
    norm_num at h
    exact h
  have h_sym1 : f 14 10 = f 10 14 := h₁ 14 10 ⟨h14pos, h10pos⟩
  have h_eq4 : (14 : ℝ) * f 10 4 = (4 : ℝ) * f 10 14 := by
    have h := h₂ 10 4 ⟨h10pos, h4pos⟩
    norm_num at h
    exact h
  have h_sym2 : f 10 4 = f 4 10 := h₁ 10 4 ⟨h10pos, h4pos⟩
  have h_eq5 : (10 : ℝ) * f 4 6 = (6 : ℝ) * f 4 10 := by
    have h := h₂ 4 6 ⟨h4pos, h6pos⟩
    norm_num at h
    exact h
  have h_sym3 : f 4 2 = f 2 4 := h₁ 4 2 ⟨h4pos, h2pos⟩
  have h_eq6 : (6 : ℝ) * f 4 2 = (2 : ℝ) * f 4 6 := by
    have h := h₂ 4 2 ⟨h4pos, h2pos⟩
    norm_num at h
    exact h
  have h_eq7 : (4 : ℝ) * f 2 2 = (2 : ℝ) * f 2 4 := by
    have h := h₂ 2 2 ⟨h2pos, h2pos⟩
    norm_num at h
    exact h
  have h_f2_2 : f 2 2 = (2 : ℝ) := h₀ 2 h2pos
  linarith
