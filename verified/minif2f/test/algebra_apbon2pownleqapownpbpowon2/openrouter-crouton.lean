import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have ha : a ∈ Set.Ici (0 : ℝ) := h₀.1.le
  have hb : b ∈ Set.Ici (0 : ℝ) := h₀.2.le
  have h := (convexOn_pow n).2 ha hb (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have e1 : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  have e2 : (1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n = (a ^ n + b ^ n) / 2 := by ring
  rw [e1, e2] at h
  exact h
