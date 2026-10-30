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
    rw [hf_expr] at h₁
    have htemp : (14 : ℂ) * (7 - z) = 0 := by
      calc
        (14 : ℂ) * (7 - z) = 98 - 14 * z := by ring
        _ = (30 - 14 * z) + 68 := by ring
        _ = (3 * ((11 - 3 * z) - 1) - 5 * z) + 68 := by ring
        _ = (-68) + 68 := by rw [h₁]
        _ = 0 := by ring
    have h14_ne_zero : (14 : ℂ) ≠ 0 := by norm_num
    have h7_minus_z_eq_zero : 7 - z = 0 := by
      rcases mul_eq_zero.mp htemp with h | h
      · exact absurd h h14_ne_zero
      · exact h
    exact (sub_eq_zero.mp h7_minus_z_eq_zero).symm
  have hf_eq : f = -10 := by
    rw [hz_eq] at hf_expr
    have hcalc : (11 : ℂ) - 3 * (7 : ℂ) = (-10 : ℂ) := by ring
    rw [hcalc] at hf_expr
    exact hf_expr
  exact And.intro hf_eq hz_eq
