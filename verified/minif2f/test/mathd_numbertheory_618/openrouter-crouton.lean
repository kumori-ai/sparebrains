import Mathlib

open scoped Nat
open scoped Real

/--
Euler discovered that the polynomial $p(n) = n^2 - n + 41$ yields prime numbers for many small positive integer values of $n$. What is the smallest positive integer $n$ for which $p(n)$ and $p(n+1)$ share a common factor greater than $1$? -/
theorem mathd_numbertheory_618 (n : ℕ) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : n > 0) (h₂ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by
  obtain ⟨q, hq_prime, hq_dvd⟩ :=
    Nat.exists_prime_and_dvd (by omega : Nat.gcd (p n) (p (n + 1)) ≠ 1)
  have hq_pn : q ∣ p n := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
  have hq_pn1 : q ∣ p (n + 1) := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
  have hle_n : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have hpn_sum : p n + n = n ^ 2 + 41 := by
    rw [h₀ n]
    omega
  have hpn1_eq : p (n + 1) = n ^ 2 + n + 41 := by
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [h₀ (n + 1), hexp]
    omega
  have hpn1_eq2 : p (n + 1) = p n + 2 * n := by omega
  have hq_2n : q ∣ 2 * n := by
    have hh := Nat.dvd_sub hq_pn1 hq_pn
    rwa [hpn1_eq2, Nat.add_sub_cancel_left] at hh
  have hmod : n ^ 2 % 2 = n % 2 := by
    have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hpow : n ^ 2 % 2 = (n % 2) ^ 2 % 2 := Nat.pow_mod n 2 2
    have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hcases with hh | hh <;> rw [hpow, hh] <;> norm_num
  have hq_164 : q ∣ 164 := by
    have h4n : q ∣ 4 * n := by
      have hh := dvd_mul_of_dvd_right hq_2n 2
      have heq : 2 * (2 * n) = 4 * n := by ring
      rwa [heq] at hh
    have h_div_sum : q ∣ 4 * p n + 4 * n :=
      dvd_add (dvd_mul_of_dvd_right hq_pn 4) h4n
    have hsq : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
    have h_eq : 4 * p n + 4 * n = (2 * n) ^ 2 + 164 := by omega
    have hh1 : q ∣ (2 * n) ^ 2 + 164 := by
      rw [h_eq] at h_div_sum
      exact h_div_sum
    have hh2 : q ∣ (2 * n) ^ 2 := dvd_pow hq_2n (by norm_num)
    have hh3 := Nat.dvd_sub hh1 hh2
    rwa [Nat.add_sub_cancel_left] at hh3
  have hq_164' : q ∣ 4 * 41 := hq_164
  rcases hq_prime.dvd_mul.mp hq_164' with h4 | h41
  · have hq2 : q ∣ 2 := by
      have hh : q ∣ 2 * 2 := h4
      rcases hq_prime.dvd_mul.mp hh with hh2 | hh2 <;> exact hh2
    have hq_eq2 : q = 2 := by
      have hle := Nat.le_of_dvd (by norm_num) hq2
      have hge := hq_prime.two_le
      omega
    subst hq_eq2
    obtain ⟨t, ht⟩ := hq_pn
    omega
  · have hq_eq41 : q = 41 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 41) q h41 with hh | hh
      · have hge := hq_prime.two_le
        omega
      · exact hh
    subst hq_eq41
    rcases (by norm_num : Nat.Prime 41).dvd_mul.mp hq_2n with hh | hh
    · have hle := Nat.le_of_dvd (by norm_num) hh
      omega
    · exact Nat.le_of_dvd h₁ hh
