import Mathlib

open scoped Nat
open scoped Real

/-- Given the equations $3x+y=17,5y+z=14$ and $3x+5z=41$, what is the value of the sum $x+y+z$? -/
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  -- Add h₀ and h₁: 3x + y + 5y + z = 17 + 14
  have h3 : 3 * x + 6 * y + z = 31 := by
    calc
      3 * x + 6 * y + z = (3 * x + y) + (5 * y + z) := by ring
      _ = 17 + 14 := by rw [h₀, h₁]
      _ = 31 := by ring
  -- Add h3 and h₂: 3x + 6y + z + 3x + 5z = 31 + 41
  have h4 : 6 * x + 6 * y + 6 * z = 72 := by
    calc
      6 * x + 6 * y + 6 * z = (3 * x + 6 * y + z) + (3 * x + 5 * z) := by ring
      _ = 31 + 41 := by rw [h3, h₂]
      _ = 72 := by ring
  -- Divide both sides by 6
  have h5 : x + y + z = 12 := by
    calc
      x + y + z = (6 * x + 6 * y + 6 * z) / 6 := by field_simp
      _ = 72 / 6 := by rw [h4]
      _ = 12 := by ring
  exact h5
