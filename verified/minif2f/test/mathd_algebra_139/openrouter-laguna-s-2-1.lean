import Mathlib

open scoped Nat
open scoped Real

/--
If $a \star b = \dfrac{\left(\dfrac{1}{b} - \dfrac{1}{a}\right)}{(a - b)}$, express $3 \star 11$ as a common fraction. -/
theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ x ≠ 0, ∀ y ≠ 0, s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by
  have h₁ : (3 : ℝ) ≠ 0 := by norm_num
  have h₂ : (11 : ℝ) ≠ 0 := by norm_num
  have h₃ : (3 : ℝ) - 11 ≠ 0 := by norm_num
  specialize h₀ 3 h₁ 11 h₂
  rw [h₀]
  field_simp
  ring
