import Mathlib

open scoped Nat
open scoped Real

/-- Find $ax^5 + by^5$ if the real numbers $a$, $b$, $x$, and $y$ satisfy the equations
\begin{eqnarray*} ax + by &=& 3, \\ ax^2 + by^2 &=& 7, \\ ax^3 + by^3 &=& 16, \\ ax^4 + by^4 &=& 42. \end{eqnarray*} -/
theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  set s : ℝ := x + y with hs
  set t : ℝ := x * y with ht
  have h3_eq : s * (a * x ^ 2 + b * y ^ 2) - t * (a * x + b * y) = a * x ^ 3 + b * y ^ 3 := by
    dsimp [s, t]
    ring
  have h3p : s * 7 - t * 3 = 16 := by
    rw [← h₁, ← h₀]
    exact h3_eq.trans h₂
  have h4_eq : s * (a * x ^ 3 + b * y ^ 3) - t * (a * x ^ 2 + b * y ^ 2) = a * x ^ 4 + b * y ^ 4 := by
    dsimp [s, t]
    ring
  have h4p : s * 16 - t * 7 = 42 := by
    rw [← h₂, ← h₁]
    exact h4_eq.trans h₃
  have h5 : s * 42 - t * 16 = 20 := by
    nlinarith [h3p, h4p]
  calc
    a * x ^ 5 + b * y ^ 5 = s * (a * x ^ 4 + b * y ^ 4) - t * (a * x ^ 3 + b * y ^ 3) := by
      dsimp [s, t]
      ring
    _ = s * 42 - t * 16 := by
      rw [h₃, h₂]
    _ = 20 := h5
