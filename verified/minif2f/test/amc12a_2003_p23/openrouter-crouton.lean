import Mathlib

open scoped Nat
open scoped Real

/-- How many perfect squares are divisors of the product $ 1!\cdot 2!\cdot 3!\cdots 9!$?

$ \textbf{(A)}\ 504 \qquad \textbf{(B)}\ 672 \qquad \textbf{(C)}\ 864 \qquad \textbf{(D)}\ 936 \qquad \textbf{(E)}\ 1008$ -/
theorem amc12a_2003_p23 (S : Finset ℕ)
    (h₀ : ∀ k : ℕ, k ∈ S ↔ 0 < k ∧ (k * k : ℕ) ∣ ∏ i ∈ Finset.Icc 1 9, i !) : S.card = 672 := by
  set P := ∏ i ∈ Finset.Icc 1 9, i ! with hPdef
  set Q := 2 ^ 15 * 3 ^ 6 * 5 ^ 2 * 7 ^ 1 with hQdef
  have hP : P = 2 ^ 30 * 3 ^ 13 * 5 ^ 5 * 7 ^ 3 := by
    rw [hPdef]
    decide
  have hPne : P ≠ 0 := by
    rw [hP]
    norm_num
  have hQne : Q ≠ 0 := by
    rw [hQdef]
    norm_num
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have hPfactF : P.factorization
      = Finsupp.single 2 30 + Finsupp.single 3 13 + Finsupp.single 5 5 + Finsupp.single 7 3 := by
    have a1 : (2 : ℕ) ^ 30 ≠ 0 := by norm_num
    have a2 : (3 : ℕ) ^ 13 ≠ 0 := by norm_num
    have a3 : (5 : ℕ) ^ 5 ≠ 0 := by norm_num
    have a4 : (7 : ℕ) ^ 3 ≠ 0 := by norm_num
    rw [hP, Nat.factorization_mul (by norm_num) a4, Nat.factorization_mul (by norm_num) a3,
      Nat.factorization_mul a1 a2]
    simp only [Nat.factorization_pow, h2.factorization, h3.factorization, h5.factorization,
      h7.factorization, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hQfactF : Q.factorization
      = Finsupp.single 2 15 + Finsupp.single 3 6 + Finsupp.single 5 2 + Finsupp.single 7 1 := by
    have a1 : (2 : ℕ) ^ 15 ≠ 0 := by norm_num
    have a2 : (3 : ℕ) ^ 6 ≠ 0 := by norm_num
    have a3 : (5 : ℕ) ^ 2 ≠ 0 := by norm_num
    have a4 : (7 : ℕ) ^ 1 ≠ 0 := by norm_num
    rw [hQdef, Nat.factorization_mul (by norm_num) a4, Nat.factorization_mul (by norm_num) a3,
      Nat.factorization_mul a1 a2]
    simp only [Nat.factorization_pow, h2.factorization, h3.factorization, h5.factorization,
      h7.factorization, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hPfact : ∀ p : ℕ, P.factorization p
      = (if 2 = p then 30 else 0) + (if 3 = p then 13 else 0)
        + (if 5 = p then 5 else 0) + (if 7 = p then 3 else 0) := by
    intro p
    rw [hPfactF]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
  have hQfact : ∀ p : ℕ, Q.factorization p
      = (if 2 = p then 15 else 0) + (if 3 = p then 6 else 0)
        + (if 5 = p then 2 else 0) + (if 7 = p then 1 else 0) := by
    intro p
    rw [hQfactF]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
  have hdiv_iff : ∀ k : ℕ, k ≠ 0 → (k * k ∣ P ↔ k ∣ Q) := by
    intro k hkne
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero hkne hkne) hPne,
      ← Nat.factorization_le_iff_dvd hkne hQne, Finsupp.le_def, Finsupp.le_def]
    apply forall_congr'
    intro p
    have hkk : (k * k).factorization p = 2 * k.factorization p := by
      rw [Nat.factorization_mul hkne hkne, Finsupp.add_apply]
      ring
    rw [hkk, hPfact p, hQfact p]
    split_ifs <;> omega
  have hSeq : S = Q.divisors := by
    ext k
    rw [h₀ k, Nat.mem_divisors]
    constructor
    · rintro ⟨hkpos, hkdiv⟩
      exact ⟨(hdiv_iff k (by omega)).mp hkdiv, hQne⟩
    · rintro ⟨hkdiv, -⟩
      exact ⟨Nat.pos_of_dvd_of_pos hkdiv (Nat.pos_of_ne_zero hQne), (hdiv_iff k (by
        intro hk
        subst hk
        exact hQne (Nat.eq_zero_of_zero_dvd hkdiv))).mpr hkdiv⟩
  rw [hSeq, Nat.card_divisors hQne]
  have hsupp_sub : Q.factorization.support ⊆ {2, 3, 5, 7} := by
    intro x hx
    rw [Finsupp.mem_support_iff, hQfact x] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h2x : x = 2
    · exact Or.inl h2x
    by_cases h3x : x = 3
    · exact Or.inr (Or.inl h3x)
    by_cases h5x : x = 5
    · exact Or.inr (Or.inr (Or.inl h5x))
    by_cases h7x : x = 7
    · exact Or.inr (Or.inr (Or.inr h7x))
    exfalso
    have h2x' : ¬ (2 = x) := fun h => h2x h.symm
    have h3x' : ¬ (3 = x) := fun h => h3x h.symm
    have h5x' : ¬ (5 = x) := fun h => h5x h.symm
    have h7x' : ¬ (7 = x) := fun h => h7x h.symm
    simp [h2x', h3x', h5x', h7x'] at hx
  have hsupp_super : ({2, 3, 5, 7} : Finset ℕ) ⊆ Q.factorization.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finsupp.mem_support_iff]
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hQfact]
  have hsupp : Q.factorization.support = {2, 3, 5, 7} :=
    Finset.Subset.antisymm hsupp_sub hsupp_super
  have hprime : Q.primeFactors = {2, 3, 5, 7} := by
    rw [← Nat.support_factorization]
    exact hsupp
  rw [hprime]
  have hprod : ∏ a ∈ ({2, 3, 5, 7} : Finset ℕ), (Q.factorization a + 1) = 672 := by
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_insert (by simp), Finset.prod_singleton,
      hQfact 2, hQfact 3, hQfact 5, hQfact 7]
    norm_num
  rw [hprod]
