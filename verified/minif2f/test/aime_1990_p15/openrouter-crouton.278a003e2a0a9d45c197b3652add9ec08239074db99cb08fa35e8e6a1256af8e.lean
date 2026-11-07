import Mathlib

open scoped Nat
open scoped Real

/-- Find $ax^5 + by^5$ if the real numbers $a$, $b$, $x$, and $y$ satisfy the equations
\begin{eqnarray*} ax + by &=& 3, \\ ax^2 + by^2 &=& 7, \\ ax^3 + by^3 &=& 16, \\ ax^4 + by^4 &=& 42. \end{eqnarray*} -/
theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  have e1 : (x + y) * 7 - (x * y) * 3 = 16 := by
    have h : (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y)
        = a * x ^ 3 + b * y ^ 3 := by ring
    rw [h₁, h₀, h₂] at h
    exact h
  have e2 : (x + y) * 16 - (x * y) * 7 = 42 := by
    have h : (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2)
        = a * x ^ 4 + b * y ^ 4 := by ring
    rw [h₂, h₁, h₃] at h
    exact h
  have e3 : (x + y) * 42 - (x * y) * 16 = a * x ^ 5 + b * y ^ 5 := by
    have h : (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3)
        = a * x ^ 5 + b * y ^ 5 := by ring
    rw [h₃, h₂] at h
    exact h
  have e4 : (x + y) * 42 - (x * y) * 16 = 20 := by
    linear_combination 38 * e1 - 14 * e2
  rw [e4] at e3
  exact e3.symm
