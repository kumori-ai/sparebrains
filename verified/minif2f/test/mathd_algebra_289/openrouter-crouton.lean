import Mathlib

open scoped Nat
open scoped Real

/--
The two positive integer solutions of the equation $x^2 - mx + n = 0$ are $k$ and $t$, where $m$ and $n$ are both prime numbers and $k > t$. What is the value of $m^n + n^m + k^t + t^k$? -/
theorem mathd_algebra_289 (k t m n : ℕ) (h₀ : Nat.Prime m ∧ Nat.Prime n) (h₁ : t < k)
    (h₂ : (k ^ 2 : ℤ) - m * k + n = 0) (h₃ : (t ^ 2 : ℤ) - m * t + n = 0) :
    m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
  obtain ⟨hm_prime, hn_prime⟩ := h₀
  push_cast at h₂ h₃
  have hkt_ne : (k : ℤ) - (t : ℤ) ≠ 0 := by
    have h : (t : ℤ) < (k : ℤ) := by exact_mod_cast h₁
    linarith
  have hfact : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := by
    have h : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ) - (m : ℤ))
        = ((k : ℤ) ^ 2 - (m : ℤ) * (k : ℤ) + (n : ℤ))
          - ((t : ℤ) ^ 2 - (m : ℤ) * (t : ℤ) + (n : ℤ)) := by ring
    rw [h, h₂, h₃]
    ring
  have hmz : (m : ℤ) = (k : ℤ) + (t : ℤ) := by
    rcases mul_eq_zero.mp hfact with h | h
    · exact absurd h hkt_ne
    · linarith
  have hm_nat : m = k + t := by exact_mod_cast hmz
  have hn_z : (n : ℤ) = (k : ℤ) * (t : ℤ) := by
    have h_eq : (n : ℤ) - (k : ℤ) * (t : ℤ)
        = ((k : ℤ) ^ 2 - (m : ℤ) * (k : ℤ) + (n : ℤ))
          + (k : ℤ) * ((m : ℤ) - ((k : ℤ) + (t : ℤ))) := by ring
    rw [h₂, hmz] at h_eq
    linarith
  have hn_nat : n = k * t := by exact_mod_cast hn_z
  have ht_dvd : t ∣ n := ⟨k, by rw [hn_nat]; ring⟩
  have ht1 : t = 1 := by
    rcases hn_prime.eq_one_or_self_of_dvd t ht_dvd with h | h
    · exact h
    · exfalso
      have hkn : k * n = 1 * n := by
        calc k * n = k * t := by rw [h]
          _ = n := hn_nat.symm
          _ = 1 * n := (one_mul n).symm
      have hk1 : k = 1 := Nat.mul_right_cancel hn_prime.pos hkn
      rw [h, hk1] at h₁
      have hpos : 1 < n := hn_prime.one_lt
      omega
  have hk_eq : k = n := by
    rw [ht1] at hn_nat
    simp at hn_nat
    exact hn_nat.symm
  have hm_eq_n : m = n + 1 := by rw [hm_nat, hk_eq, ht1]
  have hn2 : n = 2 := by
    rcases hn_prime.eq_two_or_odd with h | hodd
    · exact h
    · exfalso
      have hpos : 1 < n := hn_prime.one_lt
      rcases hm_prime.eq_two_or_odd with hm2 | hm_odd
      · rw [hm_eq_n] at hm2
        omega
      · omega
  have hm3 : m = 3 := by rw [hm_eq_n, hn2]
  have hk2 : k = 2 := by rw [hk_eq, hn2]
  rw [hm3, hn2, hk2, ht1]
  norm_num
