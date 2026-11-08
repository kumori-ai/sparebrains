import Mathlib

open scoped Nat
open scoped Real

/--
The expression $10x^2-x-24$ can be written as $(Ax-8)(Bx+3),$ where $A$ and $B$ are integers. What is $AB + B$? -/
theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 := by
  have h1 := h₀ 1
  have h2 := h₀ (-1)
  ring_nf at h1 h2
  have habR : (a : ℝ) * (b : ℝ) = 10 := by linarith
  have hlinR : 3 * (a : ℝ) - 8 * (b : ℝ) = -1 := by linarith
  have hab : a * b = 10 := by exact_mod_cast habR
  have hlin : 3 * a - 8 * b = -1 := by exact_mod_cast hlinR
  have h3a : 3 * a = 8 * b - 1 := by omega
  have h30 : 8 * b ^ 2 - b = 30 := by
    have heq : 8 * b ^ 2 - b = 3 * (a * b) := by
      calc 8 * b ^ 2 - b = b * (8 * b - 1) := by ring
        _ = b * (3 * a) := by rw [h3a]
        _ = 3 * (a * b) := by ring
    omega
  have key : (b - 2) * (8 * b + 15) = 0 := by linear_combination h30
  rcases mul_eq_zero.mp key with h | h
  · have hb : b = 2 := by omega
    calc a * b + b = 10 + b := by rw [hab]
      _ = 12 := by omega
  · omega
