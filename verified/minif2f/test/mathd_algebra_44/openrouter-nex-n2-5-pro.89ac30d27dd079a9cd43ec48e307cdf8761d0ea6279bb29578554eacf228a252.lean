import Mathlib

open scoped Nat
open scoped Real

/--
At which point do the lines $s=9-2t$ and $t=3s+1$ intersect? Give your answer as an ordered pair in the form $(s, t).$ -/
theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have ht : t = 4 := by
    calc
      t = 3 * s + 1 := h₁
      _ = 3 * (9 - 2 * t) + 1 := by rw [h₀]
      _ = 28 - 6 * t := by ring
      _ = 4 := by linarith
  have hs : s = 1 := by
    calc
      s = 9 - 2 * t := h₀
      _ = 9 - 2 * 4 := by rw [ht]
      _ = 1 := by norm_num
  exact ⟨hs, ht⟩
