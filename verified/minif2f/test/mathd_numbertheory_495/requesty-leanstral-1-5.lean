import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a$ and $b$ are positive integers such that the units digit of $a$ is $2$, the units digit of $b$ is $4$, and the greatest common divisor of $a$ and $b$ is $6$.

What is the smallest possible value of the least common multiple of $a$ and $b$? -/
theorem mathd_numbertheory_495 :
    IsLeast
      {(Nat.lcm a b) |
        (a : ℕ) (b : ℕ)
        (h₀ : 0 < a ∧ 0 < b)
        (h₁ : a % 10 = 2)
        (h₂ : b % 10 = 4)
        (h₃ : Nat.gcd a b = 6)}
      108 := by
  constructor
  · -- 108 is in the set
    refine ⟨12, 54, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 < 12 ∧ 0 < 54
      constructor <;> norm_num
    · -- 12 % 10 = 2
      norm_num
    · -- 54 % 10 = 4
      norm_num
    · -- Nat.gcd 12 54 = 6
      norm_num
    · -- 108 = Nat.lcm 12 54
      norm_num
  · -- 108 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, ⟨ha_pos, hb_pos⟩, ha_mod, hb_mod, h_gcd, hx_eq⟩
    rw [← hx_eq]
    by_cases ha : a ≥ 108
    · -- a ≥ 108
      have ha_dvd : a ∣ Nat.lcm a b := Nat.dvd_lcm_left a b
      have hlcm_pos : 0 < Nat.lcm a b := Nat.lcm_pos ha_pos hb_pos
      have ha_le : a ≤ Nat.lcm a b := Nat.le_of_dvd hlcm_pos ha_dvd
      exact le_trans ha ha_le
    · -- a < 108
      have ha_lt : a < 108 := Nat.lt_of_not_ge ha
      by_cases hb : b ≥ 108
      · -- b ≥ 108
        have hb_dvd : b ∣ Nat.lcm a b := Nat.dvd_lcm_right a b
        have hlcm_pos : 0 < Nat.lcm a b := Nat.lcm_pos ha_pos hb_pos
        have hb_le : b ≤ Nat.lcm a b := Nat.le_of_dvd hlcm_pos hb_dvd
        exact le_trans hb hb_le
      · -- b < 108
        have hb_lt : b < 108 := Nat.lt_of_not_ge hb
        have h_all : ∀ a ∈ Finset.range 108, ∀ b ∈ Finset.range 108, (0 < a ∧ 0 < b) → a % 10 = 2 → b % 10 = 4 → Nat.gcd a b = 6 → 108 ≤ Nat.lcm a b := by
          set_option maxRecDepth 10000000 in
          decide
        exact h_all a (Finset.mem_range.mpr ha_lt) b (Finset.mem_range.mpr hb_lt) ⟨ha_pos, hb_pos⟩ ha_mod hb_mod h_gcd
