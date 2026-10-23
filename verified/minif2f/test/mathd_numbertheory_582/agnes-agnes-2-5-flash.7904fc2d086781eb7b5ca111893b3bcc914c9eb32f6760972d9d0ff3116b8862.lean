import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  rw [show n + 4 + (n + 6) + (n + 8) = 3 * n + 18 by ring]
  obtain ⟨k, hk⟩ := h₁
  rw [hk]
  simp [mul_add, add_mul, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  <;> ring_nf at *
  <;> simp [Nat.mod_eq_of_lt]
  <;> omega
