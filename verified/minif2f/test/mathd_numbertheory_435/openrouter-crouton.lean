import Mathlib

open scoped Nat
open scoped Real

/--
Find the smallest positive integer $k$ such that, for every positive integer $n$, $6n+k$ is relatively prime to each of $6n+3$, $6n+2$, and $6n+1$. -/
theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by
  by_contra hlt
  push_neg at hlt
  interval_cases k
  · have h := h₃ 1
    norm_num at h
  · have h := h₂ 1
    norm_num at h
  · have h := h₁ 1
    norm_num at h
  · have h := h₂ 1
    have hd : 2 ∣ gcd (6 * 1 + 4) (6 * 1 + 2) := Nat.dvd_gcd (by norm_num) (by norm_num)
    rw [h] at hd
    norm_num at hd
