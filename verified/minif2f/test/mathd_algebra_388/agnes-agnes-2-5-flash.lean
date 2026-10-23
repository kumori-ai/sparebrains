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
  have h₂ : y = 3 * z - 8 := by
    have h₂a : 3 * (-2 * x - 3 * y + 9 * z) = 3 * (-4) := by rw [h₁]
    have h₂b : 3 * (3 * x + 4 * y - 12 * z) = 3 * 10 := by rw [h₀]
    ring_nf at h₂a h₂b
    linarith
  rw [h₂] at h₀
  ring_nf at h₀
  linarith
