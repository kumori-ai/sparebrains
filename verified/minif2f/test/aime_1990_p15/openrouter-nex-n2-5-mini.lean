import Mathlib

open scoped Nat
open scoped Real

/-- Find $ax^5 + by^5$ if the real numbers $a$, $b$, $x$, and $y$ satisfy the equations
\begin{eqnarray*} ax + by &=& 3, \\ ax^2 + by^2 &=& 7, \\ ax^3 + by^3 &=& 16, \\ ax^4 + by^4 &=& 42. \end{eqnarray*} -/
theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  have h3 : 16 = 7 * (x + y) - 3 * (x * y) := by
    calc
      16 = a * x ^ 3 + b * y ^ 3 := by rw [h₂]
      _ = (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by ring
      _ = 7 * (x + y) - 3 * (x * y) := by
        rw [h₁, h₀]
        ring

  have h4 : 42 = 16 * (x + y) - 7 * (x * y) := by
    calc
      42 = a * x ^ 4 + b * y ^ 4 := by rw [h₃]
      _ = (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by ring
      _ = 16 * (x + y) - 7 * (x * y) := by
        rw [h₂, h₁]
        ring

  have hs : x + y = -14 := by
    linarith [h3, h4]

  have hq : x * y = -38 := by
    linarith [h3, h4]

  have h5 : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring

  rw [h5]
  rw [h₃, h₂]
  rw [hs, hq]
  norm_num
