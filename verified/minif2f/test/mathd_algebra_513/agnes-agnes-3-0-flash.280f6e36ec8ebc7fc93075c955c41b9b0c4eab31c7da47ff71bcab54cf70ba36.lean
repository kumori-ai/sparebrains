import Mathlib

open scoped Nat
open scoped Real

/-- If $3a+2b=5$ and $a+b=2$, what is the ordered pair $(a,b)$ that satisfies both equations? -/
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have h₂ : b = 2 - a := by
    linarith
  have h₃ : 3 * a + 2 * (2 - a) = 5 := by
    rw [h₂] at h₀
    exact h₀
  have h₄ : a = 1 := by
    have : 3 * a + 2 * (2 - a) = 5 := h₃
    ring_nf at this ⊢
    linarith
  have h₅ : b = 1 := by
    rw [h₄] at h₂
    ring_nf at h₂ ⊢
    exact h₂
  exact ⟨h₄, h₅⟩
