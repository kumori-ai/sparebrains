import Mathlib

open scoped Nat
open scoped Real

/--
Find the smallest positive integer $k$ such that, for every positive integer $n$, $6n+k$ is relatively prime to each of $6n+3$, $6n+2$, and $6n+1$. -/
theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by
  by_contra h
  have hk : k < 5 := by omega
  interval_cases k
  · have h := h₃ 1
    exact (by decide : ¬ (gcd 7 7 = 1)) h
  · have h := h₂ 1
    exact (by decide : ¬ (gcd 8 8 = 1)) h
  · have h := h₁ 1
    exact (by decide : ¬ (gcd 9 9 = 1)) h
  · have h := h₂ 1
    exact (by decide : ¬ (gcd 10 8 = 1)) h
