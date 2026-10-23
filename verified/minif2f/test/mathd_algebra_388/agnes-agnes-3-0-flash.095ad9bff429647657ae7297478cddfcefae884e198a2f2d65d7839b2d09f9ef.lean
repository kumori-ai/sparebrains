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
  have h₂ : 9 * x + 12 * y - 36 * z = 30 := by linarith
  have h₃ : -12 * x - 18 * y + 54 * z = -24 := by linarith
  have h₄ : 0 = 0 := by linarith
  have h₅ : 15 * x = 210 := by linarith
  have h₆ : x = 14 := by linarith
  exact h₆
