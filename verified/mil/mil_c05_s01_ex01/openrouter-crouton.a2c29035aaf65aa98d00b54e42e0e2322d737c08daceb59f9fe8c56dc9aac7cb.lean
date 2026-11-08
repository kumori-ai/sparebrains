import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex01 {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  by_cases hm : Even m
  · exact even_iff_two_dvd.mp hm
  · rw [Nat.not_even_iff_odd] at hm
    obtain ⟨k, hk⟩ := hm
    obtain ⟨t, ht⟩ := h
    rw [hk] at ht
    have h2 : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    rw [h2] at ht
    omega
