import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $-a-b^2+3ab$ if $a=-1$ and $b=5$? -/
theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 := by
  subst h₀
  subst h₁
  ring
