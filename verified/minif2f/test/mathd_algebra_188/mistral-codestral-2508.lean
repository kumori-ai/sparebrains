import Mathlib

open scoped Nat
open scoped Real

/-- Suppose $f(x)$ is an invertible function, and suppose that $f(2)=f^{-1}(2)=4$.

What is the value of $f(f(2))$? -/
theorem mathd_algebra_188 (σ : ℝ ≃ ℝ) (h : σ 2 = σ.symm 2) : σ (σ 2) = 2 := by
  rw [h, σ.apply_symm_apply]
