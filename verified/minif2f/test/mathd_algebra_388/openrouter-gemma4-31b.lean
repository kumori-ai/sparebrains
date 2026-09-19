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
  -- We want to eliminate y and z.
  -- h₀: 3x + 4y - 12z = 10
  -- h₁: -2x - 3y + 9z = -4
  -- To eliminate y and z, we look for a linear combination: a*h₀ + b*h₁
  -- Coefficient of y: 4a - 3b = 0  => b = 4/3 a
  -- Coefficient of z: -12a + 9b = 0 => 9b = 12a => b = 12/9 a = 4/3 a
  -- Both conditions are the same. Let a = 3, then b = 4.
  have h₂ : 3 * (3 * x + 4 * y - 12 * z) + 4 * (-2 * x - 3 * y + 9 * z) = 3 * 10 + 4 * (-4) := by
    rw [h₀, h₁]
  simp at h₂
  -- 9x + 12y - 36z - 8x - 12y + 36z = 30 - 16
  -- x = 14
  linarith
