import Mathlib

open scoped Nat
open scoped Real

/--
The greatest common divisor of positive integers $m$ and $n$ is 8. The least common multiple of $m$ and $n$ is 112. What is the least possible value of $m+n$? -/
theorem mathd_numbertheory_711 :
    IsLeast
      { m + n | (m : ℕ) (n : ℕ)
        (h₀ : 0 < m ∧ 0 < n)
        (h₁ : gcd m n = 8)
        (h₂ : lcm m n = 112)}
      72 := by
  constructor
  · refine ⟨16, 56, ?_, ?_, ?_, by norm_num⟩
    · norm_num
    · decide
    · decide
  · rintro y ⟨m, n, hpos, hg, hl, rfl⟩
    change Nat.gcd m n = 8 at hg
    change Nat.lcm m n = 112 at hl
    have hprod : m * n = 896 := by
      have h := Nat.gcd_mul_lcm m n
      rw [hg, hl] at h
      norm_num at h
      exact h.symm
    have h8m : 8 ∣ m := by
      rw [← hg]
      exact Nat.gcd_dvd_left m n
    have h8n : 8 ∣ n := by
      rw [← hg]
      exact Nat.gcd_dvd_right m n
    obtain ⟨a, ha⟩ := h8m
    obtain ⟨b, hb⟩ := h8n
    have hab : a * b = 14 := by
      have h : (8 * a) * (8 * b) = 896 := by
        simpa [ha, hb] using hprod
      nlinarith
    have ha_pos : 0 < a := by omega
    have hb_pos : 0 < b := by omega
    have ha_le : a ≤ 14 := by
      have hb1 : 1 ≤ b := hb_pos
      have h : a * 1 ≤ a * b := Nat.mul_le_mul_left a hb1
      rw [hab] at h
      simpa using h
    have hsum : 9 ≤ a + b := by
      interval_cases a <;> norm_num at hab ⊢ <;> omega
    calc
      72 = 8 * 9 := by norm_num
      _ ≤ 8 * (a + b) := Nat.mul_le_mul_left 8 hsum
      _ = m + n := by rw [ha, hb]; ring
