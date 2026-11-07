import Mathlib

open scoped Nat
open scoped Real

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ) (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by
  have h₁' : 3 * f - 5 * z = -65 := by
    calc
      3 * f - 5 * z = (3 * (f - 1) - 5 * z) + 3 := by ring
      _ = -68 + 3 := by rw [h₁]
      _ = -65 := by ring
  have h14z : 14 * z = 98 := by
    calc
      14 * z = (3 * f + 9 * z) - (3 * f - 5 * z) := by ring
      _ = (3 * (f + 3 * z)) - (3 * f - 5 * z) := by ring
      _ = (3 * 11) - (-65) := by rw [h₀, h₁']
      _ = 98 := by ring
  have hz : z = 7 := by
    have h14 : (14 : ℂ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h14
    calc
      14 * z = 98 := h14z
      _ = 14 * 7 := by norm_num
  have hf : f = -10 := by
    calc
      f = (f + 3 * z) - 3 * z := by ring
      _ = 11 - 3 * 7 := by rw [h₀, hz]
      _ = -10 := by ring
  exact And.intro hf hz
