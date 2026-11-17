import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex03 {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro h
  have hp_dvd_m2 : p ∣ m ^ 2 := by
    rw [h]
    exact dvd_mul_right p (n ^ 2)
  have hp_dvd_m : p ∣ m := prime_p.dvd_of_dvd_pow hp_dvd_m2
  rcases hp_dvd_m with ⟨k, rfl⟩
  have hp_pos : 0 < p := prime_p.pos
  have h' : p * k ^ 2 = n ^ 2 := by
    have h1 : p * (p * k ^ 2) = p * n ^ 2 := by
      calc
        p * (p * k ^ 2) = (p * k) ^ 2 := by ring
        _ = p * n ^ 2 := h
    exact Nat.mul_left_cancel hp_pos h1
  have hp_dvd_n2 : p ∣ n ^ 2 := by
    rw [← h']
    exact dvd_mul_right p (k ^ 2)
  have hp_dvd_n : p ∣ n := prime_p.dvd_of_dvd_pow hp_dvd_n2
  have hp_dvd_gcd : p ∣ Nat.gcd (p * k) n := Nat.dvd_gcd (dvd_mul_right p k) hp_dvd_n
  have hgcd : Nat.gcd (p * k) n = 1 := coprime_mn.gcd_eq_one
  rw [hgcd] at hp_dvd_gcd
  exact prime_p.ne_one (Nat.dvd_one.mp hp_dvd_gcd)
