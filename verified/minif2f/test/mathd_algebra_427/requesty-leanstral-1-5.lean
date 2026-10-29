import Mathlib

open scoped Nat
open scoped Real

/-- Given the equations $3x+y=17,5y+z=14$ and $3x+5z=41$, what is the value of the sum $x+y+z$? -/
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  linarith
