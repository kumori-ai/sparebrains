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
  · refine ⟨12, 54, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro y hy
    obtain ⟨a, b, hpos, h1, h2, h3, rfl⟩ := hy
    obtain ⟨ha_pos, hb_pos⟩ := hpos
    have h6a : 6 ∣ a := by
      have h := Nat.gcd_dvd_left a b
      rwa [h3] at h
    have h6b : 6 ∣ b := by
      have h := Nat.gcd_dvd_right a b
      rwa [h3] at h
    obtain ⟨a', rfl⟩ := h6a
    obtain ⟨b', rfl⟩ := h6b
    have hgcd : Nat.gcd a' b' = 1 := by
      have h := h3
      rw [Nat.gcd_mul_left] at h
      omega
    have ha'_pos : 0 < a' := by omega
    have hb'_pos : 0 < b' := by omega
    have ha5 : a' % 5 = 2 := by omega
    have hb5 : b' % 5 = 4 := by omega
    have hprod : 18 ≤ a' * b' := by
      have ha_cases : a' = 2 ∨ 7 ≤ a' := by omega
      have hb_cases : b' = 4 ∨ 9 ≤ b' := by omega
      rcases ha_cases with rfl | ha7
      · rcases hb_cases with rfl | hb9
        · exfalso
          norm_num at hgcd
        · calc
            18 = 2 * 9 := rfl
            _ ≤ 2 * b' := Nat.mul_le_mul (le_refl 2) hb9
      · rcases hb_cases with rfl | hb9
        · calc
            18 ≤ 7 * 4 := by norm_num
            _ ≤ a' * 4 := Nat.mul_le_mul ha7 (le_refl 4)
        · calc
            18 ≤ 7 * 9 := by norm_num
            _ ≤ a' * b' := Nat.mul_le_mul ha7 hb9
    have hlcm : Nat.lcm (6 * a') (6 * b') = 6 * (a' * b') := by
      have h := Nat.gcd_mul_lcm (6 * a') (6 * b')
      rw [h3] at h
      have h2 : 6 * Nat.lcm (6 * a') (6 * b') = 6 * (6 * (a' * b')) := by
        rw [h]; ring
      exact mul_left_cancel₀ (by norm_num : (6 : ℕ) ≠ 0) h2
    rw [hlcm]
    calc
      108 = 6 * 18 := rfl
      _ ≤ 6 * (a' * b') := Nat.mul_le_mul (le_refl 6) hprod
