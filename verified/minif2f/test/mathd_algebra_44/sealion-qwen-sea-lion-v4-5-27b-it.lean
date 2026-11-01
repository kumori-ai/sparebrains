import Mathlib

open scoped Nat
open scoped Real

/--
At which point do the lines $s=9-2t$ and $t=3s+1$ intersect? Give your answer as an ordered pair in the form $(s, t).$ -/
theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have h_t : t = 4 := by
    have h_sub : t = 3 * (9 - 2 * t) + 1 := by rw [h₀] at h₁; exact h₁
    ring_nf at h_sub
    linarith
  have h_s : s = 1 := by
    rw [h_t] at h₀
    linarith
  exact ⟨h_s, h_t⟩
