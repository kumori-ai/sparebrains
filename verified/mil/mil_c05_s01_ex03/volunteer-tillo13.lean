import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex03 {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro h
  have hpm2 : p ∣ m ^ 2 := by
    rw [h]
    exact dvd_mul_right p (n ^ 2)
  obtain ⟨k, rfl⟩ := prime_p.dvd_of_dvd_pow hpm2
  have hk : p * k ^ 2 = n ^ 2 := by
    have h' : p * (p * k ^ 2) = p * n ^ 2 := by
      rw [← h]
      ring
    exact Nat.eq_of_mul_eq_mul_left prime_p.pos h'
  have hpn2 : p ∣ n ^ 2 := by
    rw [← hk]
    exact dvd_mul_right p (k ^ 2)
  have hpn : p ∣ n := prime_p.dvd_of_dvd_pow hpn2
  have hg : p ∣ Nat.gcd (p * k) n := Nat.dvd_gcd (dvd_mul_right p k) hpn
  rw [Nat.Coprime.gcd_eq_one coprime_mn] at hg
  exact prime_p.not_dvd_one hg
