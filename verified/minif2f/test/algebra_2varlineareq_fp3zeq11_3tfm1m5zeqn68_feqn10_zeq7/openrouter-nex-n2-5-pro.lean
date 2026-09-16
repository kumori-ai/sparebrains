import Mathlib

open scoped Nat
open scoped Real

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ) (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3 * z := by
    rw [eq_sub_iff_add_eq]
    exact h₀
  have h₃ : 30 - z * 14 = -68 := by
    rw [h₂] at h₁
    ring_nf at h₁
    exact h₁
  have h₄ : z = 7 := by
    linear_combination (-1 / 14 : ℂ) * h₃
  have h₅ : f = -10 := by
    rw [h₂, h₄]
    ring
  exact ⟨h₅, h₄⟩
