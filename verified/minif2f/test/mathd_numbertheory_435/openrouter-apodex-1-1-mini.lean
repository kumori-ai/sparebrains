import Mathlib

open scoped Nat
open scoped Real

/--
Find the smallest positive integer $k$ such that, for every positive integer $n$, $6n+k$ is relatively prime to each of $6n+3$, $6n+2$, and $6n+1$. -/
theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by
  by_contra h
  have h₄ : k ≤ 4 := by omega
  interval_cases k <;>
    (try { contradiction }) <;>
    (try {
      have h₅ := h₁ 1
      have h₆ := h₂ 1
      have h₇ := h₃ 1
      norm_num at h₅ h₆ h₇
      contradiction
    })
  all_goals (first | omega | linarith | nlinarith | positivity | decide | (norm_num; done) | (simp; done) | (aesop; done) | exact?)