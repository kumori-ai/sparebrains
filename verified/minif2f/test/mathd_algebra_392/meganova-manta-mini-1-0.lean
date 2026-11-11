import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  rcases h₀ with ⟨m, hm⟩
  have hm_pos : 0 < m := by
    by_contra! H
    have : n = 0 := by
      have hm' : n = m + m := hm
      have hm_nonpos : m = 0 := by omega
      subst hm_nonpos
      simpa [add_comm, add_left_comm, add_assoc] using hm'
    subst this
    norm_num at h₁
  have hn : (n : ℤ) = 2 * (m : ℤ) := by
    have : n = m + m := hm
    rw [this]
    push_cast
    ring
  rw [hn]
  ring_nf at h₁
  have hm_sq_eq : (m : ℤ) ^ 2 = 1024 := by
    nlinarith
  have hm_val : (m : ℤ) = 32 := by
    have hm_nonneg : 0 ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le _
    nlinarith
  rw [hm_val]
  norm_num
