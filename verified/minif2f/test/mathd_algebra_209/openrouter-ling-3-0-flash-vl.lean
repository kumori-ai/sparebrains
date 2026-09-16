import Mathlib

open scoped Nat
open scoped Real

/-- Suppose that $h(x)=f^{-1}(x)$. If $h(2)=10$, $h(10)=1$ and $h(1)=2$, what is $f(f(10))$? -/
theorem mathd_algebra_209 (σ : ℝ ≃ ℝ) (h₀ : σ.symm 2 = 10) (h₁ : σ.symm 10 = 1)
    (h₂ : σ.symm 1 = 2) : σ (σ 10) = 1 := by
  have h3 : σ 10 = 2 := by rw [← h₀, σ.apply_symm_apply]
  rw [h3]
  have h4 : σ 2 = 1 := by rw [← h₂, σ.apply_symm_apply]
  rw [h4]
