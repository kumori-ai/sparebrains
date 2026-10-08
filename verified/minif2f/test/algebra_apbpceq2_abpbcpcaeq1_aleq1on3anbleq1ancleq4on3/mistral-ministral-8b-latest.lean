import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  let S := a + b + c
  let P := a * b + b * c + c * a
  let Q := a * b * c
  have hS : S = 2 := h₁
  have hP : P = 1 := h₂
  have h₀' : a ≤ b ∧ b ≤ c := h₀
  have h₀a : a ≤ b := h₀'.left
  have h₀b : b ≤ c := h₀'.right

  -- Show a ≥ 0
  have h₁a : 0 ≤ a := by
    by_contra h_neg
    nlinarith
  -- Show a ≤ 1/3
  have h₂a : a ≤ 1 / 3 := by
    nlinarith
  -- Show 1/3 ≤ b
  have h₃b : 1 / 3 ≤ b := by
    nlinarith
  -- Show b ≤ 1
  have h₄b : b ≤ 1 := by
    linarith
  -- Show 1 ≤ c
  have h₅c : 1 ≤ c := by
    nlinarith
  -- Show c ≤ 4/3
  have h₆c : c ≤ 4 / 3 := by
    nlinarith
  -- Combine all inequalities
  exact ⟨h₁a, h₂a, h₃b, h₄b, h₅c, h₆c⟩
