import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨t, ht⟩
  have hx_ge4 : 4 ≤ x := by
    by_contra h
    have hxle3 : x ≤ 3 := by omega
    have hxle3' : (x : ℤ) ≤ 3 := by exact_mod_cast hxle3
    have hx2le : x ^ 2 ≤ 9 := by
      have hx2le_int : (x : ℤ) ^ 2 ≤ 9 := by
        have hxnonneg : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
        have hprod : 0 ≤ (3 - (x : ℤ)) * (3 + (x : ℤ)) := by
          apply mul_nonneg
          · omega
          · omega
        nlinarith
      exact_mod_cast hx2le_int
    nlinarith [hx, h₀, hx2le]
  have ht_ge3 : 3 ≤ t := by
    by_contra h
    have htle2 : t ≤ 2 := by omega
    have htle2' : (t : ℤ) ≤ 2 := by exact_mod_cast htle2
    have ht3le : t ^ 3 ≤ 8 := by
      have ht3le_int : (t : ℤ) ^ 3 ≤ 8 := by
        have hprod : 0 ≤ (2 - (t : ℤ)) * ((t : ℤ) ^ 2 + 2 * (t : ℤ) + 4) := by
          apply mul_nonneg
          · omega
          · nlinarith [sq_nonneg ((t : ℤ) + 1)]
        nlinarith
      exact_mod_cast ht3le_int
    nlinarith [ht, h₀, ht3le]
  by_contra h
  have hnle : n ≤ 63 := by omega
  have hxle7 : x ≤ 7 := by
    by_contra hxnot
    have hxge8 : 8 ≤ x := by omega
    have hxge8' : (8 : ℤ) ≤ x := by exact_mod_cast hxge8
    have hx2ge : 64 ≤ x ^ 2 := by
      have hx2ge_int : 64 ≤ (x : ℤ) ^ 2 := by
        have hprod : 0 ≤ ((x : ℤ) - 8) * ((x : ℤ) + 8) := by
          apply mul_nonneg
          · omega
          · omega
        nlinarith
      exact_mod_cast hx2ge_int
    nlinarith [hx, hnle, hx2ge]
  have htle3 : t ≤ 3 := by
    by_contra htnot
    have htge4 : 4 ≤ t := by omega
    have htge4' : (4 : ℤ) ≤ t := by exact_mod_cast htge4
    have ht3ge : 64 ≤ t ^ 3 := by
      have ht3ge_int : 64 ≤ (t : ℤ) ^ 3 := by
        have hprod : 0 ≤ ((t : ℤ) - 4) * ((t : ℤ) ^ 2 + 4 * (t : ℤ) + 16) := by
          apply mul_nonneg
          · omega
          · nlinarith [sq_nonneg ((t : ℤ) + 2)]
        nlinarith
      exact_mod_cast ht3ge_int
    nlinarith [ht, hnle, ht3ge]
  have ht_eq3 : t = 3 := by omega
  have hn_eq27 : n = 27 := by
    rw [← ht, ht_eq3]
    norm_num
  have hx2_eq27 : x ^ 2 = 27 := by
    exact hx.trans hn_eq27
  interval_cases x <;> norm_num at hx2_eq27
