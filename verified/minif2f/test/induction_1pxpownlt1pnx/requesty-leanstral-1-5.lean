import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  have hxpos : 0 < 1 + x := by linarith
  have hxpos' : 0 ≤ 1 + x := by linarith
  have hn1 : 1 ≤ n := Nat.one_le_of_lt h₁
  refine Nat.le_induction ?base (fun m hm h_ih => ?_) n hn1
  · simpa [pow_one] using le_refl (1 + x)
  · have h_ineq : 1 + ((m : ℝ) + 1) * x ≤ (1 + (m : ℝ) * x) * (1 + x) := by
      have h_eq : (1 + (m : ℝ) * x) * (1 + x) - (1 + ((m : ℝ) + 1) * x) = (m : ℝ) * x ^ 2 := by ring
      have h_nonneg : 0 ≤ (m : ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
      linarith
    calc
      1 + (↑(m+1 : ℕ) : ℝ) * x = 1 + ((m : ℝ) + 1) * x := by simp
      _ ≤ (1 + (m : ℝ) * x) * (1 + x) := h_ineq
      _ ≤ (1 + x) ^ (m : ℕ) * (1 + x) := mul_le_mul_of_nonneg_right h_ih hxpos'
      _ = (1 + x) ^ ((m : ℕ) + 1) := by rw [pow_succ]
      _ = (1 + x) ^ (m + 1) := by simp
