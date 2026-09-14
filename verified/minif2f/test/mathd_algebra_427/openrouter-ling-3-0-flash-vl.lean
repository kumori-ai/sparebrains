import Mathlib

open scoped Nat
open scoped Real

/-- Given the equations $3x+y=17,5y+z=14$ and $3x+5z=41$, what is the value of the sum $x+y+z$? -/
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h : (3 * x + y) + (5 * y + z) + (3 * x + 5 * z) = 6 * (x + y + z) := by ring
  have hsum : (3 * x + y) + (5 * y + z) + (3 * x + 5 * z) = 17 + 14 + 41 := by
    simp [h₀, h₁, h₂]
  have hval : 6 * (x + y + z) = 72 := by
    have hp : 6 * (x + y + z) = 17 + 14 + 41 := h.symm.trans hsum
    norm_num [hp]
  have hsum_val : x + y + z = 12 := by
    linarith
  exact hsum_val
