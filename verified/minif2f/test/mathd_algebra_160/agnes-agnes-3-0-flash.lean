import Mathlib

open scoped Nat
open scoped Real

/--
For each plumbing repair job, Mr. Wrench charges $N$ dollars for coming out to the house plus $x$ dollars per hour that he works at the house. He charged $\$97$ for a one-hour repair job and $\$265$ for a five-hour repair job. What is his charge for a two-hour repair job? -/
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  have h₂ : 4 * x = 168 := by
    have h₂₁ : (n + 5 * x) - (n + x) = 265 - 97 := by
      linarith
    have h₂₂ : 4 * x = 168 := by
      ring_nf at h₂₁ ⊢
      exact h₂₁
    exact h₂₂
  have h₃ : x = 42 := by
    linarith
  have h₄ : n = 55 := by
    linarith
  linarith
