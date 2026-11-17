import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ n) := convexOn_pow n
  have ha : a ∈ Set.Ici (0 : ℝ) := le_of_lt h₀.1
  have hb : b ∈ Set.Ici (0 : ℝ) := le_of_lt h₀.2
  have h := hconv.2 ha hb
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have h' : ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ^ n ≤
      (1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n := by
    simpa [smul_eq_mul] using h
  calc
    ((a + b) / 2) ^ n = ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ^ n := by
      rw [show (a + b) / 2 = (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b by ring]
    _ ≤ (1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n := h'
    _ = (a ^ n + b ^ n) / 2 := by
      ring
