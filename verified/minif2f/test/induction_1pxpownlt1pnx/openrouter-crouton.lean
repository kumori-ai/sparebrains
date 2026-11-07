import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  have hx : (0 : ℝ) < 1 + x := by linarith
  have key : ∀ m : ℕ, 1 + (m : ℝ) * x ≤ (1 + x) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      have h1 : (1 + (m : ℝ) * x) * (1 + x) ≤ (1 + x) ^ m * (1 + x) :=
        mul_le_mul_of_nonneg_right ih (le_of_lt hx)
      have hsq : (0 : ℝ) ≤ (m : ℝ) * x ^ 2 :=
        mul_nonneg (Nat.cast_nonneg m) (sq_nonneg x)
      have h2 : 1 + ((m : ℝ) + 1) * x ≤ (1 + (m : ℝ) * x) * (1 + x) := by
        have heq : (1 + (m : ℝ) * x) * (1 + x)
            = 1 + ((m : ℝ) + 1) * x + (m : ℝ) * x ^ 2 := by ring
        rw [heq]
        linarith [hsq]
      calc
        1 + ((m : ℝ) + 1) * x ≤ (1 + (m : ℝ) * x) * (1 + x) := h2
        _ ≤ (1 + x) ^ m * (1 + x) := h1
  exact key n
