import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown (m n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ x, f x = 4 ^ x + 6 ^ x + 9 ^ x) (h₁ : 0 < m ∧ 0 < n) (h₂ : m ≤ n) :
    f (2 ^ m) ∣ f (2 ^ n) := by
  rcases exists_add_of_le h₂ with ⟨k, hk⟩
  rw [hk]
  rw [h₀ (2 ^ m), h₀ (2 ^ (m + k))]
  have h_identity : ∀ a : ℕ, (4 : ℤ) ^ (2 * a) + (6 : ℤ) ^ (2 * a) + (9 : ℤ) ^ (2 * a) =
      ((4 : ℤ) ^ a + (6 : ℤ) ^ a + (9 : ℤ) ^ a) * ((4 : ℤ) ^ a + (9 : ℤ) ^ a - (6 : ℤ) ^ a) := by
    intro a
    have h4 : (4 : ℤ) ^ (2 * a) = ((4 : ℤ) ^ a) ^ 2 := by
      rw [mul_comm, ← pow_mul]
    have h6 : (6 : ℤ) ^ (2 * a) = ((6 : ℤ) ^ a) ^ 2 := by
      rw [mul_comm, ← pow_mul]
    have h9 : (9 : ℤ) ^ (2 * a) = ((9 : ℤ) ^ a) ^ 2 := by
      rw [mul_comm, ← pow_mul]
    rw [h4, h6, h9]
    have h_eq : (4 : ℤ) ^ a * (9 : ℤ) ^ a = ((6 : ℤ) ^ a) ^ 2 := by
      calc
        (4 : ℤ) ^ a * (9 : ℤ) ^ a = ((4 : ℤ) * (9 : ℤ)) ^ a := by rw [← mul_pow]
        _ = (36 : ℤ) ^ a := by norm_num
        _ = ((6 : ℤ) ^ 2) ^ a := by norm_num
        _ = ((6 : ℤ) ^ a) ^ 2 := by
          exact pow_right_comm 6 2 a
    calc
      ((4 : ℤ) ^ a) ^ 2 + ((6 : ℤ) ^ a) ^ 2 + ((9 : ℤ) ^ a) ^ 2
          = (((4 : ℤ) ^ a) ^ 2 + ((9 : ℤ) ^ a) ^ 2) + ((6 : ℤ) ^ a) ^ 2 := by ring
      _ = (((4 : ℤ) ^ a + (9 : ℤ) ^ a) ^ 2 - 2 * ((4 : ℤ) ^ a * (9 : ℤ) ^ a)) + ((6 : ℤ) ^ a) ^ 2 := by ring
      _ = (((4 : ℤ) ^ a + (9 : ℤ) ^ a) ^ 2 - 2 * ((6 : ℤ) ^ a) ^ 2) + ((6 : ℤ) ^ a) ^ 2 := by rw [h_eq]
      _ = ((4 : ℤ) ^ a + (9 : ℤ) ^ a) ^ 2 - ((6 : ℤ) ^ a) ^ 2 := by ring
      _ = ((4 : ℤ) ^ a + (6 : ℤ) ^ a + (9 : ℤ) ^ a) * ((4 : ℤ) ^ a + (9 : ℤ) ^ a - (6 : ℤ) ^ a) := by ring
  have h_div : ∀ m k, (4 : ℤ) ^ (2 ^ m) + (6 : ℤ) ^ (2 ^ m) + (9 : ℤ) ^ (2 ^ m) ∣
      (4 : ℤ) ^ (2 ^ (m + k)) + (6 : ℤ) ^ (2 ^ (m + k)) + (9 : ℤ) ^ (2 ^ (m + k)) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h_pow_eq : 2 ^ (m + (k + 1)) = 2 * (2 ^ (m + k)) := by
        grind
      rw [h_pow_eq]
      rw [h_identity (2 ^ (m + k))]
      apply dvd_trans ih
      exact dvd_mul_right _ _
  exact_mod_cast h_div m k
