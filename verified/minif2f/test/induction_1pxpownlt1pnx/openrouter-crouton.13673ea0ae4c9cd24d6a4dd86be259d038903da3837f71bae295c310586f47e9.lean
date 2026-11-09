import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  have hpos : 0 < 1 + x := by linarith
  have key : ∀ n : ℕ, 1 + (n : ℝ) * x ≤ (1 + x) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (1 + (n : ℝ) * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x) :=
        mul_le_mul_of_nonneg_right ih (le_of_lt hpos)
      have h2 : 1 + ((n : ℝ) + 1) * x ≤ (1 + (n : ℝ) * x) * (1 + x) := by
        have hnn : 0 ≤ (n : ℝ) * x ^ 2 :=
          mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)
        have heq : (1 + (n : ℝ) * x) * (1 + x)
            = 1 + ((n : ℝ) + 1) * x + (n : ℝ) * x ^ 2 := by ring
        rw [heq]
        linarith
      push_cast
      rw [pow_succ]
      linarith [h1, h2]
  exact key n
