import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 6: mul_right_eq_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L06mul_right_eq_one.lean, Apache-2.0. -/
theorem primer_advmultiplication_06_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h₀ : x ≤ 1 := by
    have h₁ : x ≠ 0 := by
      intro hx
      rw [hx] at h
      have h₂ : 0 * y = 0 := by simp
      rw [h₂] at h
      norm_num at h
    by_contra hx
    have h₂ : 1 < x := by
      omega
    have h₃ : x * y ≥ x := by
      have h₄ : 1 ≤ y := by
        by_contra hy
        have h₅ : y = 0 := by omega
        rw [h₅] at h
        have h₆ : x * 0 = 0 := by simp
        rw [h₆] at h
        norm_num at h
      nlinarith
    have h₄ : x * y > 1 := by
      have h₅ : x ≥ 2 := by omega
      have h₆ : y ≥ 1 := by omega
      have h₇ : x * y ≥ 2 * 1 := by
        nlinarith
      omega
    linarith
  have h₁ : x = 0 ∨ x = 1 := by
    omega
  have h₂ : x ≠ 0 := by
    intro hx
    rw [hx] at h
    have h₃ : 0 * y = 0 := by simp
    rw [h₃] at h
    norm_num at h
  have h₃ : x = 1 := by
    cases h₁ with
    | inl h₁ => exact (h₂ h₁).elim
    | inr h₁ => exact h₁
  exact h₃
