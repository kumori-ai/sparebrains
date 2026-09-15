import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  obtain ⟨k, rfl⟩ := h₁
  rw [show 3 * k + 4 + (3 * k + 6) + (3 * k + 8) = 9 * k + 18 by ring]
  exact Nat.mod_eq_zero_of_dvd ⟨k + 2, by ring⟩
