import Mathlib

open scoped Nat
open scoped Real

/--
The first and ninth terms of an arithmetic sequence are $\frac23$ and $\frac45$, respectively. What is the fifth term? -/
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  have e1 : a 3 - a 2 = a 2 - a 1 := h₀ 1
  have e2 : a 4 - a 3 = a 3 - a 2 := h₀ 2
  have e3 : a 5 - a 4 = a 4 - a 3 := h₀ 3
  have e4 : a 6 - a 5 = a 5 - a 4 := h₀ 4
  have e5 : a 7 - a 6 = a 6 - a 5 := h₀ 5
  have e6 : a 8 - a 7 = a 7 - a 6 := h₀ 6
  have e7 : a 9 - a 8 = a 8 - a 7 := h₀ 7
  linarith
