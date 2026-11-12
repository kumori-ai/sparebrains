import Mathlib

open scoped Nat
open scoped Real

/--
Find the smallest positive integer $k$ such that, for every positive integer $n$, $6n+k$ is relatively prime to each of $6n+3$, $6n+2$, and $6n+1$. -/
theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by
  by_contra h
  have h_k : k < 5 := by omega
  interval_cases k
  · -- k = 1: gcd(6*1+1, 6*1+1) = gcd(7,7) = 7 ≠ 1
    have h₃' := h₃ 1
    have : ¬(gcd 7 7 = 1) := by decide
    exact this h₃'
  · -- k = 2: gcd(6*0+2, 6*0+2) = gcd(2,2) = 2 ≠ 1
    have h₂' := h₂ 0
    have : ¬(gcd 2 2 = 1) := by decide
    exact this h₂'
  · -- k = 3: gcd(6*0+3, 6*0+3) = gcd(3,3) = 3 ≠ 1
    have h₁' := h₁ 0
    have : ¬(gcd 3 3 = 1) := by decide
    exact this h₁'
  · -- k = 4: gcd(6*0+4, 6*0+2) = gcd(4,2) = 2 ≠ 1
    have h₂' := h₂ 0
    have : ¬(gcd 4 2 = 1) := by decide
    exact this h₂'
