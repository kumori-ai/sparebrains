import Mathlib

open scoped Nat
open scoped Real

/-- Find $ax^5 + by^5$ if the real numbers $a$, $b$, $x$, and $y$ satisfy the equations
\begin{eqnarray*} ax + by &=& 3, \\ ax^2 + by^2 &=& 7, \\ ax^3 + by^3 &=& 16, \\ ax^4 + by^4 &=& 42. \end{eqnarray*} -/
theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  set p := x + y with hp
  set q := x * y with hq
  have h₄ : 7 * p - 3 * q = 16 := by
    calc
      7 * p - 3 * q = p * (a * x ^ 2 + b * y ^ 2) - q * (a * x + b * y) := by rw [h₁, h₀]; ring
      _ = a * x ^ 3 + b * y ^ 3 := by ring
      _ = 16 := h₂
  have h₅ : 16 * p - 7 * q = 42 := by
    calc
      16 * p - 7 * q = p * (a * x ^ 3 + b * y ^ 3) - q * (a * x ^ 2 + b * y ^ 2) := by rw [h₂, h₁]; ring
      _ = a * x ^ 4 + b * y ^ 4 := by ring
      _ = 42 := h₃
  have h₆ : p = -14 := by
    have h₆a : 49 * p - 21 * q = 112 := by
      calc
        49 * p - 21 * q = 7 * (7 * p - 3 * q) := by ring
        _ = 7 * 16 := by rw [h₄]
        _ = 112 := by norm_num
    have h₆b : 48 * p - 21 * q = 126 := by
      calc
        48 * p - 21 * q = 3 * (16 * p - 7 * q) := by ring
        _ = 3 * 42 := by rw [h₅]
        _ = 126 := by norm_num
    calc
      p = (49 * p - 21 * q) - (48 * p - 21 * q) := by ring
      _ = 112 - 126 := by rw [h₆a, h₆b]
      _ = -14 := by norm_num
  have h₇ : q = -38 := by
    have h₇a : 3 * q = -114 := by
      calc
        3 * q = 7 * p - 16 := by linarith [h₄]
        _ = 7 * (-14) - 16 := by rw [h₆]
        _ = -114 := by norm_num
    linarith [h₇a]
  have h₈ : a * x ^ 5 + b * y ^ 5 = p * (a * x ^ 4 + b * y ^ 4) - q * (a * x ^ 3 + b * y ^ 3) := by
    calc
      a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by ring
      _ = p * (a * x ^ 4 + b * y ^ 4) - q * (a * x ^ 3 + b * y ^ 3) := by rw [hp, hq]
  rw [h₈, h₆, h₇, h₃, h₂]
  norm_num
