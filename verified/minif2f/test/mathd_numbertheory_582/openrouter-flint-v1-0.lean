import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  rcases h₁ with ⟨k, hk⟩
  have hdiv : 9 ∣ (n + 4 + (n + 6) + (n + 8)) := by
    use k + 2
    rw [hk]
    ring
  exact (Nat.dvd_iff_mod_eq_zero.mp hdiv)
