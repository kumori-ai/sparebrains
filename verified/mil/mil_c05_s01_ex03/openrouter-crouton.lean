import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex03 {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro h
  have hp_pos : 0 < p := prime_p.pos
  have hpm : p ∣ m := prime_p.dvd_of_dvd_pow ⟨n ^ 2, h⟩
  have hpm_copy := hpm
  obtain ⟨k, hk⟩ := hpm_copy
  have h2 : p * k ^ 2 = n ^ 2 := by
    have h' : p * (p * k ^ 2) = p * n ^ 2 := by
      calc p * (p * k ^ 2) = (p * k) ^ 2 := by ring
      _ = m ^ 2 := by rw [hk]
      _ = p * n ^ 2 := h
    exact Nat.mul_left_cancel hp_pos h'
  have hpn : p ∣ n := prime_p.dvd_of_dvd_pow ⟨k ^ 2, h2.symm⟩
  have hpgcd : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
  have hgcd : Nat.gcd m n = 1 := coprime_mn
  rw [hgcd] at hpgcd
  have hp1 : p = 1 := Nat.dvd_one.mp hpgcd
  exact prime_p.ne_one hp1
