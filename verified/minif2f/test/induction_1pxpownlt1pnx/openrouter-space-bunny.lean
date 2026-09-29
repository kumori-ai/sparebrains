import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  have hmain : ∀ m : ℕ, 1 + (m : ℝ) * x ≤ (1 + x) ^ m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hpos : 0 < 1 + x := by
          linarith
        have hsq : 0 ≤ (m : ℝ) * x ^ 2 :=
          mul_nonneg (Nat.cast_nonneg m) (sq_nonneg x)
        calc
          1 + (Nat.succ m : ℝ) * x ≤
              (1 + (m : ℝ) * x) * (1 + x) := by
                have hcast : (Nat.succ m : ℝ) = (m : ℝ) + 1 := by
                  simp
                rw [hcast]
                nlinarith [hsq]
          _ ≤ (1 + x) ^ m * (1 + x) :=
            mul_le_mul_of_nonneg_right ih (le_of_lt hpos)
          _ = (1 + x) ^ Nat.succ m := by
            rw [pow_succ]
  exact hmain n
