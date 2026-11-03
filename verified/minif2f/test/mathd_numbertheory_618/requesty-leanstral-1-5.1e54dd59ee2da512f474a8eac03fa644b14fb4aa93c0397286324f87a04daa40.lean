import Mathlib

open scoped Nat
open scoped Real

/--
Euler discovered that the polynomial $p(n) = n^2 - n + 41$ yields prime numbers for many small positive integer values of $n$. What is the smallest positive integer $n$ for which $p(n)$ and $p(n+1)$ share a common factor greater than $1$? -/
theorem mathd_numbertheory_618 (n : ℕ) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : n > 0) (h₂ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by
  by_contra! h
  have h_all : ∀ k : ℕ, k < 41 → 0 < k → Nat.gcd (k ^ 2 - k + 41) ((k + 1) ^ 2 - (k + 1) + 41) = 1 := by
    decide
  have h_gcd_eq_one : Nat.gcd (p n) (p (n + 1)) = 1 := by
    rw [h₀ n, h₀ (n + 1)]
    exact h_all n h h₁
  rw [h_gcd_eq_one] at h₂
  exact lt_irrefl 1 h₂
