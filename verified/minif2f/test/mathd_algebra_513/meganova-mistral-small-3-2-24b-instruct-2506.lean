import Mathlib

open scoped Nat
open scoped Real

/-- If $3a+2b=5$ and $a+b=2$, what is the ordered pair $(a,b)$ that satisfies both equations? -/
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have h₂ : b = 2 - a := by linarith [h₁]
  rw [h₂] at h₀
  have h₃ : 3 * a + 2 * (2 - a) = 5 := by linarith [h₀]
  ring_nf at h₃
  have h₄ : 3 * a + 4 - 2 * a = 5 := by linarith [h₃]
  ring_nf at h₄
  have h₅ : a + 4 = 5 := by linarith [h₄]
  have h₆ : a = 1 := by linarith [h₅]
  have h₇ : b = 1 := by linarith [h₂, h₆]
  exact ⟨h₆, h₇⟩
