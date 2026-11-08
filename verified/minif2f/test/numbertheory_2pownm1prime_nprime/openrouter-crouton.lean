import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  have hn1 : n ≠ 1 := by
    intro h
    subst h
    norm_num at h₁
  have hn2 : 2 ≤ n := by omega
  set p := n.minFac with hp_def
  have hp_prime : Nat.Prime p := Nat.minFac_prime hn1
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_le : p ≤ n := Nat.le_of_dvd h₀ hp_dvd
  have hp_ge : 2 ≤ p := hp_prime.two_le
  have hp_eq : p = n := by
    by_contra hne
    have hp_lt : p < n := lt_of_le_of_ne hp_le hne
    obtain ⟨k, hk⟩ := hp_dvd
    have hge : 4 ≤ 2 ^ p := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp_ge
    have hpow_lt : 2 ^ p < 2 ^ n := pow_lt_pow_right₀ (by norm_num) hp_lt
    set m := 2 ^ p - 1 with hm_def
    have hm_gt : 1 < m := by omega
    have hm_lt : m < 2 ^ n - 1 := by omega
    have hmod : 2 ^ p ≡ 1 [MOD m] := by
      have h1 : 2 ^ p = m + 1 := by omega
      unfold Nat.ModEq
      rw [h1, Nat.add_comm m 1, Nat.add_mod_right]
    have hmodn : 2 ^ n ≡ 1 [MOD m] := by
      have h := hmod.pow k
      rw [one_pow] at h
      rwa [← pow_mul, ← hk] at h
    have hdvd : m ∣ 2 ^ n - 1 := by
      have hle : (1 : ℕ) ≤ 2 ^ n := by
        calc (1 : ℕ) = 2 ^ 0 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.zero_le n)
      exact (Nat.modEq_iff_dvd' hle).mp hmodn.symm
    have hcases := h₁.eq_one_or_self_of_dvd m hdvd
    rcases hcases with h | h
    · omega
    · omega
  rw [hp_eq] at hp_prime
  exact hp_prime
