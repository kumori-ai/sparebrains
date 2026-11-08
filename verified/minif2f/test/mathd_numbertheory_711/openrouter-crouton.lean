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
  refine ⟨?_, ?_⟩
  · refine ⟨16, 56, ⟨by norm_num, by norm_num⟩, by decide, by decide, rfl⟩
  · intro x hx
    obtain ⟨m, n, h0, h1, h2, rfl⟩ := hx
    have hm8 : 8 ∣ m := h1 ▸ Nat.gcd_dvd_left m n
    have hn8 : 8 ∣ n := h1 ▸ Nat.gcd_dvd_right m n
    obtain ⟨a, rfl⟩ := hm8
    obtain ⟨b, rfl⟩ := hn8
    have ha_pos : 0 < a := by
      have h := h0.1
      omega
    have hb_pos : 0 < b := by
      have h := h0.2
      omega
    have h1n : Nat.gcd (8 * a) (8 * b) = 8 := h1
    have h2n : Nat.lcm (8 * a) (8 * b) = 112 := h2
    have h1' : 8 * Nat.gcd a b = 8 := by
      rw [Nat.gcd_mul_left] at h1n
      exact h1n
    have h2' : 8 * Nat.lcm a b = 112 := by
      rw [Nat.lcm_mul_left] at h2n
      exact h2n
    have hgcd : Nat.gcd a b = 1 := by omega
    have hlcm : Nat.lcm a b = 14 := by omega
    have hab : a * b = 14 := by
      have h := Nat.gcd_mul_lcm a b
      rw [hgcd, hlcm] at h
      omega
    have ha_le : a ≤ 14 := Nat.le_of_dvd (by norm_num) ⟨b, hab.symm⟩
    have hb_le : b ≤ 14 :=
      Nat.le_of_dvd (by norm_num) ⟨a, by rw [mul_comm]; exact hab.symm⟩
    interval_cases a <;> interval_cases b <;> omega
