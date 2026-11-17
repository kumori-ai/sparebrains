import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h₁)
  clear h₁
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hx : 0 < 1 + x := by linarith
      have hmul : (1 + ↑(Nat.succ m) * x) * (1 + x) ≤
          (1 + x) ^ (Nat.succ m) * (1 + x) :=
        mul_le_mul_of_nonneg_right ih (le_of_lt hx)
      have hpoly : 1 + ↑(Nat.succ (Nat.succ m)) * x ≤
          (1 + ↑(Nat.succ m) * x) * (1 + x) := by
        have hprod : (0 : ℝ) ≤ (↑m + 1) * x ^ 2 := by positivity
        push_cast
        nlinarith [hprod]
      calc
        1 + ↑(Nat.succ (Nat.succ m)) * x ≤
            (1 + ↑(Nat.succ m) * x) * (1 + x) := hpoly
        _ ≤ (1 + x) ^ (Nat.succ m) * (1 + x) := hmul
        _ = (1 + x) ^ (Nat.succ (Nat.succ m)) := by
          simpa using (pow_succ (1 + x) (Nat.succ m)).symm
