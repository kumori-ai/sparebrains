import Mathlib

open scoped Nat
open scoped Real

/--
We have two geometric sequences of positive real numbers: $$6,a,b\text{ and }\frac{1}{b},a,54$$Solve for $a$. -/
theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 := by
  rcases h₀ with ⟨ha_pos, hb_pos⟩
  have ha_pos' : (0 : ℝ) < a := by exact_mod_cast ha_pos
  have hb_pos' : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have ha_nonneg : 0 ≤ (a : ℝ) := by exact_mod_cast ha_pos.le
  have h₁' : (a : ℝ)^2 = 6 * (b : ℝ) := by exact_mod_cast h₁
  have h₂' : (a : ℝ)^2 = 54 / (b : ℝ) := by exact_mod_cast h₂
  have hb_ne_zero : (b : ℝ) ≠ 0 := by linarith
  have h_eq : 6 * (b : ℝ) = 54 / (b : ℝ) := by
    calc
      6 * (b : ℝ) = (a : ℝ)^2 := by symm; exact h₁'
      _ = 54 / (b : ℝ) := h₂'
  field_simp [hb_ne_zero] at h_eq
  -- h_eq : (6 * b) * b = 54
  have hb_sq_eq : (b : ℝ)^2 = 9 := by
    nlinarith
  have hb_eq : (b : ℝ) = 3 := by
    nlinarith
  have ha_sq_eq : (a : ℝ)^2 = 18 := by
    calc
      (a : ℝ)^2 = 6 * (b : ℝ) := h₁'
      _ = 6 * 3 := by rw [hb_eq]
      _ = 18 := by norm_num
  have ha_eq : (a : ℝ) = 3 * Real.sqrt 2 := by
    calc
      (a : ℝ) = Real.sqrt ((a : ℝ)^2) := by rw [Real.sqrt_sq ha_nonneg]
      _ = Real.sqrt 18 := by rw [ha_sq_eq]
      _ = Real.sqrt (9 * 2) := by norm_num
      _ = Real.sqrt 9 * Real.sqrt 2 := by rw [Real.sqrt_mul (show (0 : ℝ) ≤ 9 from by norm_num) 2]
      _ = 3 * Real.sqrt 2 := by norm_num
  apply NNReal.eq
  simpa [NNReal.coe_mul] using ha_eq
