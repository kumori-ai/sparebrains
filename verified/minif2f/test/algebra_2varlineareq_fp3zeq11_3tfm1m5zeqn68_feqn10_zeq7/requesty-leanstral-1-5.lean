import Mathlib

open scoped Nat
open scoped Real

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ) (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by
  have hf_expr : f = 11 - 3 * z := by
    calc
      f = (f + 3 * z) - 3 * z := by ring
      _ = 11 - 3 * z := by rw [h₀]
  have hz_eq : z = 7 := by
    have htemp : -14 * z = -98 := by
      calc
        -14 * z = (3 * ((11 - 3 * z) - 1) - 5 * z) - 30 := by ring
        _ = (-68) - 30 := by
          rw [hf_expr] at h₁
          rw [h₁]
        _ = -98 := by ring
    have h14 : (14 : ℂ) ≠ 0 := by norm_num
    have htemp2 : (14 : ℂ) * z = 98 := by
      calc
        (14 : ℂ) * z = -(-14 * z) := by ring
        _ = -(-98) := by rw [htemp]
        _ = 98 := by ring
    have hz_eq' : z = 7 := by
      apply mul_left_cancel₀ h14
      calc
        (14 : ℂ) * z = 98 := htemp2
        _ = (14 : ℂ) * 7 := by norm_num
    exact hz_eq'
  have hf : f = -10 := by
    calc
      f = 11 - 3 * z := hf_expr
      _ = 11 - 3 * (7 : ℂ) := by rw [hz_eq]
      _ = -10 := by ring
  exact And.intro hf hz_eq
