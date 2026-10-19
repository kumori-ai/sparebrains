import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h₁ : 0 < 1 + abs (a + b) := by
    have h₁₁ : 0 ≤ abs (a + b) := abs_nonneg (a + b)
    linarith
  
  have h₂ : 0 < 1 + abs a := by
    have h₂₁ : 0 ≤ abs a := abs_nonneg a
    linarith
  
  have h₃ : 0 < 1 + abs b := by
    have h₃₁ : 0 ≤ abs b := abs_nonneg b
    linarith
  
  have h₄ : abs (a + b) ≤ abs a + abs b := by
    exact abs_add_le a b
  have h₅ : abs (a + b) * (1 + abs a + abs b) ≤ (abs a + abs b) * (1 + abs (a + b)) := by
    have h₅₁ : 0 ≤ abs (a + b) := abs_nonneg (a + b)
    have h₅₂ : 0 ≤ abs a := abs_nonneg a
    have h₅₃ : 0 ≤ abs b := abs_nonneg b
    have h₅₄ : abs (a + b) ≤ abs a + abs b := h₄
    nlinarith [sq_nonneg (abs (a + b) - (abs a + abs b)), sq_nonneg (abs a - abs b)]
  
  have h₆ : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs a + abs b) := by
    have h₆₁ : 0 < 1 + abs a + abs b := by linarith
    have h₆₂ : 0 < (1 + abs (a + b)) * (1 + abs a + abs b) := by positivity
    -- Use the fact that the function f(x) = x / (1 + x) is increasing for x ≥ 0
    have h₆₃ : abs (a + b) * (1 + abs a + abs b) ≤ (abs a + abs b) * (1 + abs (a + b)) := h₅
    -- Divide both sides by the positive denominators
    have h₆₄ : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs a + abs b) := by
      exact (div_le_div_iff₀ h₁ h₆₁).mpr h₅
    exact h₆₄
  
  have h₇ : 0 ≤ abs a := by
    exact abs_nonneg a
  
  have h₈ : 0 ≤ abs b := by
    exact abs_nonneg b
  
  have h₉ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    have h₉₁ : 0 < 1 + abs a := by linarith
    have h₉₂ : 0 < 1 + abs b := by linarith
    have h₉₃ : 0 < 1 + abs a + abs b := by linarith
    have h₉₄ : 0 < (1 + abs a) * (1 + abs b) := by positivity
    have h₉₅ : 0 < (1 + abs a + abs b) * (1 + abs a) * (1 + abs b) := by positivity
    -- Cross-multiply to eliminate denominators
    have h₉₆ : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
      field_simp
      ring_nf
      nlinarith
    exact h₉₆
  
  have h₁₀ : abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    linarith [h₆, h₉]
  
  exact h₁₀
