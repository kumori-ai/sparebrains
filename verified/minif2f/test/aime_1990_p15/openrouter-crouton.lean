import Mathlib

open scoped Nat
open scoped Real

/-- Find $ax^5 + by^5$ if the real numbers $a$, $b$, $x$, and $y$ satisfy the equations
\begin{eqnarray*} ax + by &=& 3, \\ ax^2 + by^2 &=& 7, \\ ax^3 + by^3 &=& 16, \\ ax^4 + by^4 &=& 42. \end{eqnarray*} -/
theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  have r1 : a * x ^ 3 + b * y ^ 3
      = (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by ring
  have r2 : a * x ^ 4 + b * y ^ 4
      = (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by ring
  have r3 : a * x ^ 5 + b * y ^ 5
      = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by ring
  rw [h₂, h₁, h₀] at r1
  rw [h₃, h₂, h₁] at r2
  rw [h₃, h₂] at r3
  rw [r3]
  linarith
