import Mathlib

open scoped Nat
open scoped Real

/--
For each plumbing repair job, Mr. Wrench charges $N$ dollars for coming out to the house plus $x$ dollars per hour that he works at the house. He charged $\$97$ for a one-hour repair job and $\$265$ for a five-hour repair job. What is his charge for a two-hour repair job? -/
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  have h₂ : 4 * x = 168 := by
    linarith
  have h₃ : x = 42 := by
    linarith
  have h₄ : n = 55 := by
    linarith
  have h₅ : n + 2 * x = 139 := by
    linarith
  exact h₅
