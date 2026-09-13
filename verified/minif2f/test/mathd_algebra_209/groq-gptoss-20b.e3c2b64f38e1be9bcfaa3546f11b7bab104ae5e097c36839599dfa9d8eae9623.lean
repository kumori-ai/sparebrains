import Mathlib

open scoped Nat
open scoped Real

/-- Suppose that $h(x)=f^{-1}(x)$. If $h(2)=10$, $h(10)=1$ and $h(1)=2$, what is $f(f(10))$? -/
theorem mathd_algebra_209 (σ : ℝ ≃ ℝ) (h₀ : σ.symm 2 = 10) (h₁ : σ.symm 10 = 1)
    (h₂ : σ.symm 1 = 2) : σ (σ 10) = 1 := by
  -- From `h₀` we get `σ 10 = 2`
  have h10 : σ 10 = 2 := by
    have : 2 = σ 10 := by
      simpa using congrArg σ h₀
    simpa [eq_comm] using this
  -- From `h₂` we get `σ 2 = 1`
  have h2' : σ 2 = 1 := by
    have : 1 = σ 2 := by
      simpa using congrArg σ h₂
    simpa [eq_comm] using this
  -- Now compute
  calc
    σ (σ 10) = σ 2 := by simpa [h10]
    _ = 1 := h2'
