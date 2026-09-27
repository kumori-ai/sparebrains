import Mathlib

open scoped Nat
open scoped Real

/--
The first and ninth terms of an arithmetic sequence are $\frac23$ and $\frac45$, respectively. What is the fifth term? -/
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  have h₃ : a 3 - a 2 = a 2 - a 1 := by
    simpa using h₀ 1
  have h₄ : a 4 - a 3 = a 3 - a 2 := by
    simpa using h₀ 2
  have h₅ : a 5 - a 4 = a 4 - a 3 := by
    simpa using h₀ 3
  have h₆ : a 6 - a 5 = a 5 - a 4 := by
    simpa using h₀ 4
  have h₇ : a 7 - a 6 = a 6 - a 5 := by
    simpa using h₀ 5
  have h₈ : a 8 - a 7 = a 7 - a 6 := by
    simpa using h₀ 6
  have h₉ : a 9 - a 8 = a 8 - a 7 := by
    simpa using h₀ 7
  linarith
