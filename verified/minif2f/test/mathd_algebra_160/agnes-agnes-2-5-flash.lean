import Mathlib

open scoped Nat
open scoped Real

/--
For each plumbing repair job, Mr. Wrench charges $N$ dollars for coming out to the house plus $x$ dollars per hour that he works at the house. He charged $\$97$ for a one-hour repair job and $\$265$ for a five-hour repair job. What is his charge for a two-hour repair job? -/
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  have h₂ : x = 42 := by
    have : 4 * x = 168 := by linarith
    linarith
  have h₃ : n = 55 := by linarith
  rw [h₃, h₂]
  norm_num
