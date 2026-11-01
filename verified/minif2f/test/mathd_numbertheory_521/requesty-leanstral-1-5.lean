import Mathlib

open scoped Nat
open scoped Real

/--
The product of two consecutive positive even integers is 288. What is the greater of the two integers? -/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have hle : n ≤ m := by omega
  have hmn : m = n + 2 := by omega
  rcases h₁ with ⟨b, hn⟩
  have hnz : (n : ℤ) = 2 * (b : ℤ) := by
    exact_mod_cast (show n = 2 * b by simpa [two_mul] using hn)
  have hmz : (m : ℤ) = (n : ℤ) + 2 := by exact_mod_cast hmn
  rw [hnz] at hmz
  have hprod_z : (m : ℤ) * (n : ℤ) = 288 := by exact_mod_cast h₃
  rw [hmz, hnz] at hprod_z
  ring_nf at hprod_z
  have hb_nonneg : 0 ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le b
  have hb_eq_8 : (b : ℤ) = 8 := by
    nlinarith
  have hm_eq_18 : (m : ℤ) = 18 := by
    rw [hmz, hb_eq_8]
    norm_num
  exact_mod_cast hm_eq_18
