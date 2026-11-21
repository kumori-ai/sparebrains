import Mathlib

open scoped Nat
open scoped Real

/--
A positive integer $n$ is nice if there is a positive integer $m$ with exactly four positive divisors (including $1$ and $m$) such that the sum of the four divisors is equal to $n.$ Find the sum of all the nice numbers in the set $\{ 2010,2011,2012,\dots,2019 \}.$ -/
theorem mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ ∑ p ∈ Nat.divisors m, p = n) :
    ∑ k ∈ S, k = 2016 := by
  have quotient_coprime : ∀ (m p : ℕ) (hp : Nat.Prime p) (hpm : p ∣ m) (hn : ¬ p ^ 2 ∣ m), Nat.Coprime p (m / p) := by
    intro m p hp hpm hn
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    apply hn
    have hmul : p * p ∣ p * (m / p) := Nat.mul_dvd_mul_left p hd
    simpa [pow_two, Nat.mul_div_cancel' hpm] using hmul
  have quotient_divisor_count : ∀ (m p : ℕ) (hc : (Nat.divisors m).card = 4) (hp : Nat.Prime p) (hpm : p ∣ m) (hn : ¬ p ^ 2 ∣ m), 2 * (Nat.divisors (m / p)).card = 4 := by
    intro m p hc hp hpm hn
    have hcop := quotient_coprime m p hp hpm hn
    have hcount := Nat.Coprime.card_divisors_mul hcop
    have hpc : (Nat.divisors p).card = 2 := by
      rw [hp.divisors]
      simp [Ne.symm hp.ne_one]
    rw [Nat.mul_div_cancel' hpm, hc, hpc] at hcount
    exact hcount.symm
  have prime_of_two_divisors : ∀ (n : ℕ) (hc : (Nat.divisors n).card = 2), Nat.Prime n := by
    intro n hc
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      simp at hc
    have hn1 : n ≠ 1 := by
      intro h
      subst n
      simp at hc
    have hsub : ({1, n} : Finset ℕ) ⊆ Nat.divisors n := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_refl _, hn0⟩
    have heq : ({1, n} : Finset ℕ) = Nat.divisors n :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hc, Ne.symm hn1])
    apply Nat.prime_def_lt.mpr
    refine ⟨by omega, ?_⟩
    intro d hlt hd
    have hmem := Nat.mem_divisors.mpr ⟨hd, hn0⟩
    rw [← heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact h
    · omega
  have prime_factor_branch : ∀ (m p : ℕ) (hc : (Nat.divisors m).card = 4) (hp : Nat.Prime p) (hpm : p ∣ m) (hn : ¬ p ^ 2 ∣ m), ∃ q : ℕ, Nat.Prime q ∧ p ≠ q ∧ m = p * q := by
    intro m p hc hp hpm hn
    have hcount := quotient_divisor_count m p hc hp hpm hn
    have hprime : Nat.Prime (m / p) := prime_of_two_divisors (m / p) (by omega)
    have hneq : p ≠ m / p := by
      intro heq
      apply hn
      have hm : m = p * p := by
        calc
          m = p * (m / p) := (Nat.mul_div_cancel' hpm).symm
          _ = p * p := by rw [← heq]
      rw [hm, pow_two]
    exact ⟨m / p, hprime, hneq, (Nat.mul_div_cancel' hpm).symm⟩
  have prime_product_divisor_sum : ∀ (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q), ∑ d ∈ Nat.divisors (p * q), d = (p + 1) * (q + 1) := by
    intro p q hp hq hne
    have hcop : Nat.Coprime p q := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      rcases (Nat.dvd_prime hq).mp hd with h | h
      · exact hp.ne_one h
      · exact hne h
    rw [hcop.sum_divisors_mul, hp.divisors, hq.divisors]
    simp [Ne.symm hp.ne_one, Ne.symm hq.ne_one, Nat.add_comm]
  have nonsquare_branch_sum : ∀ (m p : ℕ) (hc : (Nat.divisors m).card = 4) (hp : Nat.Prime p) (hpm : p ∣ m) (hn : ¬ p ^ 2 ∣ m), ∃ q : ℕ, Nat.Prime q ∧ p ≠ q ∧ ∑ d ∈ Nat.divisors m, d = (p + 1) * (q + 1) := by
    intro m p hc hp hpm hn
    obtain ⟨q, hq, hne, hm⟩ := prime_factor_branch m p hc hp hpm hn
    refine ⟨q, hq, hne, ?_⟩
    rw [hm]
    exact prime_product_divisor_sum p q hp hq hne
  have square_factor_branch : ∀ (m p : ℕ) (hc : (Nat.divisors m).card = 4) (hp : Nat.Prime p) (hsq : p ^ 2 ∣ m), m = p ^ 3 := by
    intro m p hc hp hsq
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      simp at hc
    have hp2 := hp.two_le
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hle : p ^ 2 ≤ m := Nat.le_of_dvd hmpos hsq
    have hnot : m ≠ p ^ 2 := by
      intro h
      rw [h, Nat.divisors_prime_pow hp] at hc
      simp at hc
    have hpm : p ∣ m := dvd_trans (by simp [pow_two]) hsq
    have hsub : ({1, p, p ^ 2, m} : Finset ℕ) ⊆ Nat.divisors m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h | h
      · subst d
        exact Nat.mem_divisors.mpr ⟨one_dvd m, hm0⟩
      · subst d
        exact Nat.mem_divisors.mpr ⟨hpm, hm0⟩
      · subst d
        exact Nat.mem_divisors.mpr ⟨hsq, hm0⟩
      · subst d
        exact Nat.mem_divisors.mpr ⟨dvd_refl _, hm0⟩
    have h1p : (1 : ℕ) ≠ p := by omega
    have h1sq : (1 : ℕ) ≠ p ^ 2 := by nlinarith
    have h1m : (1 : ℕ) ≠ m := by nlinarith
    have hpsq : p ≠ p ^ 2 := by nlinarith
    have hpmne : p ≠ m := by nlinarith
    have hsqm : p ^ 2 ≠ m := Ne.symm hnot
    have heq : ({1, p, p ^ 2, m} : Finset ℕ) = Nat.divisors m :=
      Finset.eq_of_subset_of_card_le hsub (by
        simp [hc, h1p, h1sq, h1m, hpsq, hpmne, hsqm])
    have hmul : (m / p) * p = m := Nat.div_mul_cancel hpm
    have hmem : m / p ∈ Nat.divisors m :=
      Nat.mem_divisors.mpr ⟨⟨p, hmul.symm⟩, hm0⟩
    rw [← heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [h] at hmul
      nlinarith
    · rw [h] at hmul
      exact False.elim (hnot (by nlinarith))
    · rw [h] at hmul
      calc
        m = p ^ 2 * p := hmul.symm
        _ = p ^ 3 := by ring
    · rw [h] at hmul
      nlinarith
  have four_divisor_classification : ∀ (m : ℕ) (hc : (Nat.divisors m).card = 4), (∃ p : ℕ, Nat.Prime p ∧ m = p ^ 3) ∨ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ m = p * q) := by
    intro m hc
    have hm1 : m ≠ 1 := by
      intro h
      subst m
      simp at hc
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    by_cases hsq : p ^ 2 ∣ m
    · exact Or.inl ⟨p, hp, square_factor_branch m p hc hp hsq⟩
    · obtain ⟨q, hq, hne, hm⟩ := prime_factor_branch m p hc hp hpm hsq
      exact Or.inr ⟨p, q, hp, hq, hne, hm⟩
  have four_divisor_sum_classification : ∀ (m : ℕ) (hc : (Nat.divisors m).card = 4), (∃ p : ℕ, Nat.Prime p ∧ ∑ d ∈ Nat.divisors m, d = 1 + p + p ^ 2 + p ^ 3) ∨ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ ∑ d ∈ Nat.divisors m, d = (p + 1) * (q + 1)) := by
    intro m hc
    rcases four_divisor_classification m hc with ⟨p, hp, hm⟩ | ⟨p, q, hp, hq, hne, hm⟩
    · refine Or.inl ⟨p, hp, ?_⟩
      rw [hm, Nat.sum_divisors_prime_pow hp]
      simp [Finset.sum_range_succ]
    · refine Or.inr ⟨p, q, hp, hq, hne, ?_⟩
      rw [hm]
      exact prime_product_divisor_sum p q hp hq hne
  have small_prime_product_window : ∀ (p q : ℕ) (hp : Nat.Prime p) (hsmall : p ≤ 43) (hq : Nat.Prime q) (hlo : 2010 ≤ (p + 1) * (q + 1)) (hhi : (p + 1) * (q + 1) ≤ 2019), (p + 1) * (q + 1) = 2016 := by
    intro p q hp hsmall hq hlo hhi
    have hbounds : 2010 / (p + 1) - 1 ≤ q ∧ q ≤ 2019 / (p + 1) - 1 := by
      constructor
      · have hdiv : 2010 / (p + 1) ≤ ((p + 1) * (q + 1)) / (p + 1) :=
          Nat.div_le_div_right hlo
        have hlo' : 2010 / (p + 1) ≤ q + 1 := by
          simpa using hdiv
        omega
      · have hdiv : q + 1 ≤ 2019 / (p + 1) :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
        omega
    interval_cases p
    all_goals norm_num at hp
    all_goals norm_num at hbounds
    all_goals rcases hbounds with ⟨hql, hqu⟩
    all_goals interval_cases q
    all_goals first | omega | (norm_num at hq)
  have prime_product_window : ∀ (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hlo : 2010 ≤ (p + 1) * (q + 1)) (hhi : (p + 1) * (q + 1) ≤ 2019), (p + 1) * (q + 1) = 2016 := by
    intro p q hp hq hlo hhi
    have hsmall : p ≤ 43 ∨ q ≤ 43 := by
      by_cases h : p ≤ 43
      · exact Or.inl h
      · right
        by_contra hq'
        have hp44 : 44 ≤ p := by omega
        have hq44 : 44 ≤ q := by omega
        nlinarith
    rcases hsmall with h | h
    · exact small_prime_product_window p q hp h hq hlo hhi
    · have hlo' : 2010 ≤ (q + 1) * (p + 1) := by nlinarith
      have hhi' : (q + 1) * (p + 1) ≤ 2019 := by nlinarith
      simpa [Nat.mul_comm] using small_prime_product_window q p hq h hp hlo' hhi'
  have cube_sum_outside_window : ∀ (p : ℕ), ¬ (2010 ≤ 1 + p + p ^ 2 + p ^ 3 ∧ 1 + p + p ^ 2 + p ^ 3 ≤ 2019) := by
    intro p
    rintro ⟨hlo, hhi⟩
    have hbound : p ≤ 12 := by
      by_contra h
      have hp13 : 13 ≤ p := by omega
      have hs : 13 ^ 2 ≤ p ^ 2 := by nlinarith
      have ht : 13 ^ 3 ≤ p ^ 3 := by nlinarith [pow_two p, pow_two 13]
      omega
    interval_cases p <;> omega
  have witness_2016 : (Nat.divisors 1837).card = 4 ∧ ∑ d ∈ Nat.divisors 1837, d = 2016 := by
    have hp : Nat.Prime 11 := by norm_num
    have hq : Nat.Prime 167 := by norm_num
    constructor
    · rw [show 1837 = 11 * 167 by norm_num]
      rw [(show Nat.Coprime 11 167 by decide).card_divisors_mul, hp.divisors, hq.divisors]
      norm_num
    · have h := prime_product_divisor_sum 11 167 hp hq (by decide)
      norm_num at h
      exact h
  have hmem : ∀ n : ℕ, n ∈ S ↔ n = 2016 := by
    intro n
    constructor
    · intro hn
      obtain ⟨hlo, hhi, m, hc, hsum⟩ := (h₀ n).mp hn
      rcases four_divisor_sum_classification m hc with ⟨p, hp, hs⟩ | ⟨p, q, hp, hq, hne, hs⟩
      · exact False.elim (cube_sum_outside_window p (by omega))
      · have hlo' : 2010 ≤ (p + 1) * (q + 1) := by omega
        have hhi' : (p + 1) * (q + 1) ≤ 2019 := by omega
        have h := prime_product_window p q hp hq hlo' hhi'
        omega
    · intro hn
      subst n
      exact (h₀ 2016).mpr ⟨by decide, by decide, 1837, witness_2016⟩
  have hS : S = {2016} := by
    ext n
    simpa using hmem n
  rw [hS]
  simp
