import Mathlib

open scoped Nat
open scoped Real

/--
At which point do the lines $s=9-2t$ and $t=3s+1$ intersect? Give your answer as an ordered pair in the form $(s, t).$ -/
theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  constructor
  · linarith
  · linarith
