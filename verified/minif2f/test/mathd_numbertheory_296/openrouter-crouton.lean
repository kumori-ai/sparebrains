import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest positive integer, other than $1$, that is both a perfect cube and a perfect fourth power? -/
theorem mathd_numbertheory_296 : IsLeast {n : ℕ | 2 ≤ n ∧ ∃ x, x ^ 3 = n ∧ ∃ t, t ^ 4 = n} 4096 := by
  constructor
  · refine ⟨by norm_num, 16, by norm_num, 8, by norm_num⟩
  · intro n hn
    obtain ⟨hn2, x, hx, t, ht⟩ := hn
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · subst h; simp at hx; omega
      · exact h
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at ht; omega
      · exact h
    set d := Nat.gcd x t with hd_def
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left x t) hxpos
    obtain ⟨a, ha⟩ := Nat.gcd_dvd_left x t
    obtain ⟨b, hb⟩ := Nat.gcd_dvd_right x t
    have hapos : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at ha; omega
      · exact h
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hb; omega
      · exact h
    have ha_div : x / d = a := by
      rw [ha]; exact Nat.mul_div_cancel_left a hdpos
    have hb_div : t / d = b := by
      rw [hb]; exact Nat.mul_div_cancel_left b hdpos
    have hcop_ab : Nat.Coprime a b := by
      have h := Nat.coprime_div_gcd_div_gcd (m := x) (n := t) hdpos
      rw [ha_div, hb_div] at h
      exact h
    have heq : (d * a) ^ 3 = (d * b) ^ 4 := by
      rw [← ha, ← hb, hx, ht]
    have heq2 : a ^ 3 = d * b ^ 4 := by
      have h1 : d ^ 3 * a ^ 3 = d ^ 3 * (d * b ^ 4) := by
        calc d ^ 3 * a ^ 3 = (d * a) ^ 3 := by ring
        _ = (d * b) ^ 4 := heq
        _ = d ^ 3 * (d * b ^ 4) := by ring
      exact mul_left_cancel₀ (pow_ne_zero 3 (by omega : d ≠ 0)) h1
    have hdiv : b ^ 4 ∣ a ^ 3 := ⟨d, by rw [heq2]; ring⟩
    have hcop_pow : Nat.Coprime (a ^ 3) (b ^ 4) := Nat.Coprime.pow 3 4 hcop_ab
    have hb4 : b ^ 4 = 1 := by
      have hgcd1 : Nat.gcd (a ^ 3) (b ^ 4) = 1 := hcop_pow
      have hgcd2 : Nat.gcd (a ^ 3) (b ^ 4) = b ^ 4 := Nat.gcd_eq_right hdiv
      rw [hgcd1] at hgcd2
      exact hgcd2.symm
    have hb1 : b = 1 := by
      by_contra hbne
      have hb2 : 2 ≤ b := by omega
      have hle : (2 : ℕ) ^ 4 ≤ b ^ 4 := Nat.pow_le_pow_left hb2 4
      norm_num at hle
      omega
    have hd_eq : d = a ^ 3 := by
      rw [hb1] at heq2
      simpa using heq2.symm
    have hn_eq : n = a ^ 12 := by
      calc n = x ^ 3 := hx.symm
      _ = (d * a) ^ 3 := by rw [ha]
      _ = a ^ 12 := by rw [hd_eq]; ring
    have ha2 : 2 ≤ a := by
      by_contra h
      have ha1 : a = 1 := by omega
      rw [ha1] at hn_eq
      norm_num at hn_eq
      omega
    calc (4096 : ℕ) = 2 ^ 12 := by norm_num
    _ ≤ a ^ 12 := Nat.pow_le_pow_left ha2 12
    _ = n := hn_eq.symm
