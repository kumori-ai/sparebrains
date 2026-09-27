import Mathlib

open scoped Nat
open scoped Real

/--
The first and ninth terms of an arithmetic sequence are $\frac23$ and $\frac45$, respectively. What is the fifth term? -/
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  linarith [h₀ 1, h₀ 2, h₀ 3, h₀ 4, h₀ 5, h₀ 6, h₀ 7]
