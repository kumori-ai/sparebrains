import Mathlib

open scoped Nat
open scoped Real

/--
The product of two positive whole numbers is 2005. If neither number is 1, what is the sum of the two numbers? -/
theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by
  have h5 : Nat.Prime 5 := by norm_num
  have h401 : Nat.Prime 401 := by norm_num
  have key : ∀ x : ℕ, x ∣ 2005 → x = 1 ∨ x = 5 ∨ x = 401 ∨ x = 2005 := by
    intro x hx
    rw [show (2005 : ℕ) = 5 * 401 by norm_num] at hx
    by_cases h5dvd : 5 ∣ x
    · obtain ⟨x', rfl⟩ := h5dvd
      have hx' : x' ∣ 401 := (mul_dvd_mul_iff_left (by norm_num)).mp hx
      rcases (Nat.dvd_prime h401).mp hx' with rfl | rfl
      · omega
      · omega
    · have hcop : Nat.Coprime x 5 := ((h5.coprime_iff_not_dvd).mpr h5dvd).symm
      have hx401 : x ∣ 401 := hcop.dvd_of_dvd_mul_left hx
      rcases (Nat.dvd_prime h401).mp hx401 with rfl | rfl
      · omega
      · omega
  have hm := key m ⟨n, h₂.symm⟩
  rcases hm with rfl | rfl | rfl | rfl <;> omega
