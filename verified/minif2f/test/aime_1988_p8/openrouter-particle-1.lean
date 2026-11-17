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
  have hA := h₂ 14 38 (by norm_num)
  norm_num at hA
  have hB := h₂ 14 24 (by norm_num)
  norm_num at hB
  have hC := h₂ 14 10 (by norm_num)
  norm_num at hC
  have hSym1 := h₁ 14 10 (by norm_num)
  have hD := h₂ 10 4 (by norm_num)
  norm_num at hD
  have hSym2 := h₁ 10 4 (by norm_num)
  have hE := h₂ 4 6 (by norm_num)
  norm_num at hE
  have hF := h₂ 4 2 (by norm_num)
  norm_num at hF
  have hSym3 := h₁ 4 2 (by norm_num)
  have hG := h₂ 2 2 (by norm_num)
  norm_num at hG
  have h22 := h₀ 2 (by norm_num)
  norm_num at h22
  nlinarith [hA, hB, hC, hSym1, hD, hSym2, hE, hF, hSym3, hG, h22]
