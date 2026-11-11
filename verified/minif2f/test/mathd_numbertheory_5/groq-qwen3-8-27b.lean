import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  by_contra h
  have h_n_lt_64 : n < 64 := by omega
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  have h_t_ge_3 : 3 ≤ t := by
    by_contra h'
    have : t ≤ 2 := by omega
    have : t ^ 3 ≤ 8 := by
      have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      rcases this with (rfl | rfl | rfl) <;> norm_num
    have : n ≤ 8 := by
      calc n = t ^ 3 := ht.symm
        _ ≤ 8 := by assumption
    omega
  have h_t_le_3 : t ≤ 3 := by
    by_contra h'
    have : t ≥ 4 := by omega
    have : t ^ 3 ≥ 64 := by
      calc t ^ 3 ≥ 4 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 64 := by norm_num
    have : n ≥ 64 := by
      calc n = t ^ 3 := ht.symm
        _ ≥ 64 := by assumption
    omega
  have h_t_eq_3 : t = 3 := by omega
  have h_n_eq_27 : n = 27 := by
    calc n = t ^ 3 := ht.symm
      _ = 3 ^ 3 := by rw [h_t_eq_3]
      _ = 27 := by norm_num
  have h_x_sq_27 : x ^ 2 = 27 := by
    calc x ^ 2 = n := hx
      _ = 27 := h_n_eq_27
  have h_x_ge_5 : 5 ≤ x := by
    by_contra h'
    have : x ≤ 4 := by omega
    have : x ^ 2 ≤ 16 := by
      have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
      rcases this with (rfl | rfl | rfl | rfl | rfl) <;> norm_num
    have : n ≤ 16 := by
      calc n = x ^ 2 := hx.symm
        _ ≤ 16 := by assumption
    omega
  have h_x_le_5 : x ≤ 5 := by
    by_contra h'
    have : x ≥ 6 := by omega
    have : x ^ 2 ≥ 36 := by
      calc x ^ 2 ≥ 6 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 36 := by norm_num
    have : n ≥ 36 := by
      calc n = x ^ 2 := hx.symm
        _ ≥ 36 := by assumption
    omega
  have h_x_eq_5 : x = 5 := by omega
  rw [h_x_eq_5] at h_x_sq_27
  norm_num at h_x_sq_27
