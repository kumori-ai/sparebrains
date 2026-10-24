import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have h₅ : b = 1 - a := by linarith
  have h₆ : d = 1 - c := by linarith
  have h₇ : b - d = c - a := by linarith
  have h₈ : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    have h₈a : a ^ 2 + a = 1 := by linarith
    have h₈b : c ^ 2 + c = 1 := by linarith
    have h₈c : (a + c) = -1 := by
      have h₈c₁ : (a - c) * (a + c) = a ^ 2 - c ^ 2 := by ring
      have h₈c₂ : a ^ 2 + a = c ^ 2 + c := by linarith
      have h₈c₃ : a ^ 2 - c ^ 2 = -(a - c) := by linarith
      have h₈c₄ : (a - c) * (a + c) = -(a - c) := by linarith
      have h₈c₅ : a - c ≠ 0 := by intro h; apply h₄; linarith
      have h₈c₆ : a + c = -1 := by apply mul_left_cancel₀ h₈c₅; linarith
      exact h₈c₆
    have h₈d : a * c = -1 := by
      have h₈d₁ : a ^ 2 + a = 1 := by linarith
      have h₈d₂ : c ^ 2 + c = 1 := by linarith
      have h₈d₃ : a ^ 2 - c ^ 2 + a - c = 0 := by linarith
      have h₈d₄ : (a - c) * (a + c) + (a - c) = 0 := by linarith
      have h₈d₅ : (a - c) * (a + c + 1) = 0 := by linarith
      have h₈d₆ : a + c + 1 = 0 := by
        apply mul_left_cancel₀ (show a - c ≠ 0 by intro h; apply h₄; linarith)
        linarith
      nlinarith
    nlinarith
  rw [h₈]
  <;> simp [Real.sqrt_eq_iff_sq_eq]
