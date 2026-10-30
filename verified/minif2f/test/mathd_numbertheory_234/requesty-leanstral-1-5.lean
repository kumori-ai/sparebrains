import Mathlib

open scoped Nat
open scoped Real

/--
When the two-digit integer $``\text{AB}"$ is cubed, the value is $912,\!673$. What is $A + B$? -/
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  rcases h₀ with ⟨ha1, ha9, hb9⟩
  have h10a_b_ge_10 : 10 ≤ 10 * a + b := by
    omega
  have h10a_b_le_99 : 10 * a + b ≤ 99 := by
    omega
  have h_mem_Icc : 10 * a + b ∈ Finset.Icc 10 99 := by
    exact Finset.mem_Icc.mpr ⟨h10a_b_ge_10, h10a_b_le_99⟩
  have h_candidates_eq : (Finset.filter (λ n => n ^ 3 = 912673) (Finset.Icc 10 99)) = {97} := by
    decide
  have h_mem_filter : 10 * a + b ∈ Finset.filter (λ n => n ^ 3 = 912673) (Finset.Icc 10 99) := by
    apply Finset.mem_filter.mpr
    exact ⟨h_mem_Icc, h₁⟩
  rw [h_candidates_eq] at h_mem_filter
  have h_eq : 10 * a + b = 97 := by
    simpa using h_mem_filter
  have ha9' : a = 9 := by
    omega
  have hb7 : b = 7 := by
    omega
  rw [ha9', hb7]
