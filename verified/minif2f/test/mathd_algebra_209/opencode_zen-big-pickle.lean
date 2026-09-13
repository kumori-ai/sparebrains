import Mathlib

open scoped Nat
open scoped Real

/-- Suppose that $h(x)=f^{-1}(x)$. If $h(2)=10$, $h(10)=1$ and $h(1)=2$, what is $f(f(10))$? -/
theorem mathd_algebra_209 (σ : ℝ ≃ ℝ) (h₀ : σ.symm 2 = 10) (h₁ : σ.symm 10 = 1)
    (h₂ : σ.symm 1 = 2) : σ (σ 10) = 1 := by
  have hσ10 : σ 10 = 2 := by
    rw [← h₀]
    exact Equiv.apply_symm_apply σ 2
  have hσ2 : σ 2 = 1 := by
    rw [← h₂]
    exact Equiv.apply_symm_apply σ 1
  rw [hσ10, hσ2]
