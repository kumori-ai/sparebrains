import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  rcases h₁ with ⟨k, hk⟩
  have hsum : n + 4 + (n + 6) + (n + 8) = 9 * (k + 2) := by
    calc
      n + 4 + (n + 6) + (n + 8)
          = 3 * n + 18 := by ring
      _ = 3 * (3 * k) + 18 := by simpa [hk]
      _ = 9 * k + 18 := by ring
      _ = 9 * (k + 2) := by ring
  have hdiv : 9 ∣ n + 4 + (n + 6) + (n + 8) := by
    have : 9 ∣ 9 * (k + 2) := by
      exact dvd_mul_right 9 (k + 2)
    simpa [hsum] using this
  exact Nat.mod_eq_zero_of_dvd hdiv
