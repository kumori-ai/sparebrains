import Mathlib

open scoped Nat
open scoped Real

/--
The first and ninth terms of an arithmetic sequence are $\frac23$ and $\frac45$, respectively. What is the fifth term? -/
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  have h₃ := h₀ 0
  have h₄ := h₀ 1
  have h₅ := h₀ 2
  have h₆ := h₀ 3
  have h₇ := h₀ 4
  have h₈ := h₀ 5
  have h₉ := h₀ 6
  have h₁₀ := h₀ 7
  linarith
