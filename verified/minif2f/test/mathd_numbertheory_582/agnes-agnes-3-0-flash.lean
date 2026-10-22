import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  have h₂ : n % 3 = 0 := by
    omega
  have h₃ : ∃ k : ℕ, n = 3 * k := by
    omega
  obtain ⟨k, hk⟩ := h₃
  have h₄ : (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
    subst_vars
    ring_nf
    omega
  exact h₄
