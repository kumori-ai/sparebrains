import Mathlib

open scoped Nat
open scoped Real

/-- If

\begin{align*}
3x+4y-12z&=10,\\
-2x-3y+9z&=-4,
\end{align*}

compute $x$. -/
theorem mathd_algebra_388 (x y z : ℝ) (h₀ : 3 * x + 4 * y - 12 * z = 10)
    (h₁ : -2 * x - 3 * y + 9 * z = -4) : x = 14 := by
  have h₂ : 9 * x + 12 * y - 36 * z = 30 := by
    calc
      9 * x + 12 * y - 36 * z = 3 * (3 * x + 4 * y - 12 * z) := by ring
      _ = 3 * 10 := by rw [h₀]
      _ = 30 := by norm_num
  have h₃ : -8 * x - 12 * y + 36 * z = -16 := by
    calc
      -8 * x - 12 * y + 36 * z = 4 * (-2 * x - 3 * y + 9 * z) := by ring
      _ = 4 * (-4) := by rw [h₁]
      _ = -16 := by norm_num
  linarith [h₂, h₃]
