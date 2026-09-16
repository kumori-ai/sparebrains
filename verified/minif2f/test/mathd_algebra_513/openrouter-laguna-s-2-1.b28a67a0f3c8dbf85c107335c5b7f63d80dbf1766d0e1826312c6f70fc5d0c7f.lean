import Mathlib

open scoped Nat
open scoped Real

/-- If $3a+2b=5$ and $a+b=2$, what is the ordered pair $(a,b)$ that satisfies both equations? -/
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have ha : a = 1 := by
    calc
      a = (3 * a + 2 * b) - 2 * (a + b) := by ring
      _ = 5 - 2 * 2 := by rw [h₀, h₁]
      _ = 1 := by ring
  have hb : b = 1 := by
    calc
      b = (a + b) - a := by ring
      _ = 2 - 1 := by rw [h₁, ha]
      _ = 1 := by ring
  exact ⟨ha, hb⟩
