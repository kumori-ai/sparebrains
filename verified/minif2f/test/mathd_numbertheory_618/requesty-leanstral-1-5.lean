import Mathlib

open scoped Nat
open scoped Real

/--
Euler discovered that the polynomial $p(n) = n^2 - n + 41$ yields prime numbers for many small positive integer values of $n$. What is the smallest positive integer $n$ for which $p(n)$ and $p(n+1)$ share a common factor greater than $1$? -/
theorem mathd_numbertheory_618 (n : ℕ) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : n > 0) (h₂ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by
  by_contra! hlt
  -- hlt : n < 41
  have h_coprime : ∀ n, n ∈ Finset.Icc 1 40 → Nat.gcd (n ^ 2 - n + 41) ((n + 1) ^ 2 - (n + 1) + 41) = 1 := by
    decide
  have hpn : p n = n ^ 2 - n + 41 := h₀ n
  have hpn1 : p (n + 1) = (n + 1) ^ 2 - (n + 1) + 41 := h₀ (n + 1)
  have h1le : 1 ≤ n := by omega
  have hnle40 : n ≤ 40 := by omega
  have hn_mem : n ∈ Finset.Icc 1 40 := Finset.mem_Icc.mpr ⟨h1le, hnle40⟩
  have hgcd1 : Nat.gcd (p n) (p (n + 1)) = 1 := by
    rw [hpn, hpn1]
    exact h_coprime n hn_mem
  rw [hgcd1] at h₂
  exact lt_irrefl 1 h₂
