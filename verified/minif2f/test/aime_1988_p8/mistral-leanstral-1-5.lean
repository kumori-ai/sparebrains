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
  have h2 : 0 < (2 : ℕ) := by decide
  have h4 : 0 < (4 : ℕ) := by decide
  have h6 : 0 < (6 : ℕ) := by decide
  have h10 : 0 < (10 : ℕ) := by decide
  have h14 : 0 < (14 : ℕ) := by decide
  have h24 : 0 < (24 : ℕ) := by decide
  have h38 : 0 < (38 : ℕ) := by decide
  have h52 : 0 < (52 : ℕ) := by decide
  have hf22 : f 2 2 = (2 : ℝ) := by
    simpa using h₀ 2 h2
  have hf24 : f 2 4 = (4 : ℝ) := by
    have h := h₂ 2 2 ⟨h2, h2⟩
    norm_num at h
    rw [hf22] at h
    norm_num at h
    linarith
  have hf42 : f 4 2 = (4 : ℝ) := by
    rw [h₁ 4 2 ⟨h4, h2⟩, hf24]
  have hf46 : f 4 6 = (12 : ℝ) := by
    have h := h₂ 4 2 ⟨h4, h2⟩
    norm_num at h
    rw [hf42] at h
    norm_num at h
    linarith
  have hf410 : f 4 10 = (20 : ℝ) := by
    have h := h₂ 4 6 ⟨h4, h6⟩
    norm_num at h
    rw [hf46] at h
    norm_num at h
    linarith
  have hf104 : f 10 4 = (20 : ℝ) := by
    rw [h₁ 10 4 ⟨h10, h4⟩, hf410]
  have hf1014 : f 10 14 = (70 : ℝ) := by
    have h := h₂ 10 4 ⟨h10, h4⟩
    norm_num at h
    rw [hf104] at h
    norm_num at h
    linarith
  have hf1410 : f 14 10 = (70 : ℝ) := by
    rw [h₁ 14 10 ⟨h14, h10⟩, hf1014]
  have hf1424 : f 14 24 = (168 : ℝ) := by
    have h := h₂ 14 10 ⟨h14, h10⟩
    norm_num at h
    rw [hf1410] at h
    norm_num at h
    linarith
  have hf1438 : f 14 38 = (266 : ℝ) := by
    have h := h₂ 14 24 ⟨h14, h24⟩
    norm_num at h
    rw [hf1424] at h
    norm_num at h
    linarith
  have hf1452 : f 14 52 = (364 : ℝ) := by
    have h := h₂ 14 38 ⟨h14, h38⟩
    norm_num at h
    rw [hf1438] at h
    norm_num at h
    linarith
  exact hf1452
