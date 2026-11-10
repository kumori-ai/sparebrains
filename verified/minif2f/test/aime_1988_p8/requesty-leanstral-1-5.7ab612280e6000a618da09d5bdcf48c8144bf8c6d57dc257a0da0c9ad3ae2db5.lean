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
  have h14 : 0 < 14 := by norm_num
  have h52 : 0 < 52 := by norm_num
  have h10 : 0 < 10 := by norm_num
  have h24 : 0 < 24 := by norm_num
  have h38 : 0 < 38 := by norm_num
  have h4 : 0 < 4 := by norm_num
  have h6 : 0 < 6 := by norm_num
  have h2 : 0 < 2 := by norm_num
  have h2_14_38' : (52 : ℝ) * f 14 38 = (38 : ℝ) * f 14 52 := by
    have h := h₂ 14 38 ⟨h14, h38⟩
    norm_num at h
    exact h
  have h2_14_24' : (38 : ℝ) * f 14 24 = (24 : ℝ) * f 14 38 := by
    have h := h₂ 14 24 ⟨h14, h24⟩
    norm_num at h
    exact h
  have h2_14_10' : (24 : ℝ) * f 14 10 = (10 : ℝ) * f 14 24 := by
    have h := h₂ 14 10 ⟨h14, h10⟩
    norm_num at h
    exact h
  have h_sym_14_10 : f 14 10 = f 10 14 := h₁ 14 10 ⟨h14, h10⟩
  have h2_10_4' : (14 : ℝ) * f 10 4 = (4 : ℝ) * f 10 14 := by
    have h := h₂ 10 4 ⟨h10, h4⟩
    norm_num at h
    exact h
  have h_sym_10_4 : f 10 4 = f 4 10 := h₁ 10 4 ⟨h10, h4⟩
  have h2_4_6' : (10 : ℝ) * f 4 6 = (6 : ℝ) * f 4 10 := by
    have h := h₂ 4 6 ⟨h4, h6⟩
    norm_num at h
    exact h
  have h2_4_2' : (6 : ℝ) * f 4 2 = (2 : ℝ) * f 4 6 := by
    have h := h₂ 4 2 ⟨h4, h2⟩
    norm_num at h
    exact h
  have h_sym_4_2 : f 4 2 = f 2 4 := h₁ 4 2 ⟨h4, h2⟩
  have h2_2_2' : (4 : ℝ) * f 2 2 = (2 : ℝ) * f 2 4 := by
    have h := h₂ 2 2 ⟨h2, h2⟩
    norm_num at h
    exact h
  have h0_2 : f 2 2 = (2 : ℝ) := h₀ 2 h2
  linarith
