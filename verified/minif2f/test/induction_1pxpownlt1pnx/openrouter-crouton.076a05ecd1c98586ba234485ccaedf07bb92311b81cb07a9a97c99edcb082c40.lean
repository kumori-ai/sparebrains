import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction n, h₁ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hx : (0 : ℝ) ≤ 1 + x := by linarith
    have hmul : (1 + (n : ℝ) * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x) :=
      mul_le_mul_of_nonneg_right ih hx
    have hnn : (0 : ℝ) ≤ (n : ℝ) * x ^ 2 :=
      mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)
    have hexp : (1 + (n : ℝ) * x) * (1 + x) = 1 + ((n : ℝ) + 1) * x + (n : ℝ) * x ^ 2 := by ring
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    calc
      1 + ((n + 1 : ℕ) : ℝ) * x = 1 + ((n : ℝ) + 1) * x := by rw [hcast]
      _ ≤ 1 + ((n : ℝ) + 1) * x + (n : ℝ) * x ^ 2 := by linarith
      _ = (1 + (n : ℝ) * x) * (1 + x) := hexp.symm
      _ ≤ (1 + x) ^ n * (1 + x) := hmul
      _ = (1 + x) ^ (n + 1) := (pow_succ (1 + x) n).symm
