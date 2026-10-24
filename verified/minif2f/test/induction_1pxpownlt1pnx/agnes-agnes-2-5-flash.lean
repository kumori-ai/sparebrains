import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction' h₁ with n hn IH
  · norm_num
  · have h₂ : 0 < 1 + x := by linarith
    have h₃ : (1 + x : ℝ) ^ (n + 1) = (1 + x) ^ n * (1 + x) := by ring
    have h₄ : (1 + x : ℝ) ^ n * (1 + x) ≥ (1 + (n : ℝ) * x) * (1 + x) := by
      have h₅ : 0 < 1 + x := by linarith
      have h₆ : (1 + x : ℝ) ^ n ≥ 1 + (n : ℝ) * x := by exact_mod_cast IH
      nlinarith
    have h₇ : (1 + (n : ℝ) * x) * (1 + x) = 1 + ((n : ℕ) + 1 : ℝ) * x + (n : ℝ) * x ^ 2 := by ring
    have h₈ : 1 + ((n : ℕ) + 1 : ℝ) * x + (n : ℝ) * x ^ 2 ≥ 1 + ((n : ℕ) + 1 : ℝ) * x := by
      have h₉ : 0 ≤ (n : ℝ) * x ^ 2 := by positivity
      linarith
    have h₁₀ : 1 + ((n : ℕ) + 1 : ℝ) * x = 1 + ↑(n.succ) * x := by norm_cast
    calc
      (1 + x : ℝ) ^ (n + 1) ≥ (1 + (n : ℝ) * x) * (1 + x) := h₄
      _ = 1 + ((n : ℕ) + 1 : ℝ) * x + (n : ℝ) * x ^ 2 := by rw [h₇]
      _ ≥ 1 + ((n : ℕ) + 1 : ℝ) * x := h₈
      _ = 1 + ↑(n.succ) * x := by rw [h₁₀]
