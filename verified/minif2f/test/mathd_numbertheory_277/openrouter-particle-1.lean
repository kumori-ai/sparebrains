import Mathlib

open scoped Nat
open scoped Real

/--
The greatest common divisor of positive integers $m$ and $n$ is 6. The least common multiple of $m$ and $n$ is 126. What is the least possible value of $m+n$? -/
theorem mathd_numbertheory_277 :
    IsLeast
       {(m + n) | (m : ℕ) (n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126)}
      60 := by
  constructor
  · refine ⟨18, 42, by norm_num, by norm_num, by norm_num⟩
  · intro y hy
    rcases hy with ⟨m, n, hgcd, hlcm, rfl⟩
    have hprod : m * n = 756 := by
      have h := Nat.gcd_mul_lcm m n
      rw [hgcd, hlcm] at h
      norm_num at h
      exact h.symm
    have h6m : 6 ∣ m := by
      simpa [hgcd] using Nat.gcd_dvd_left m n
    have h6n : 6 ∣ n := by
      simpa [hgcd] using Nat.gcd_dvd_right m n
    rcases h6m with ⟨a, rfl⟩
    rcases h6n with ⟨b, rfl⟩
    have hab : a * b = 21 := by
      nlinarith [hprod]
    have ha_pos : 0 < a := by
      by_contra h
      have ha0 : a = 0 := Nat.eq_zero_of_not_pos h
      rw [ha0, zero_mul] at hab
      omega
    have hb_pos : 0 < b := by
      by_contra h
      have hb0 : b = 0 := Nat.eq_zero_of_not_pos h
      rw [hb0, mul_zero] at hab
      omega
    have ha_le : a ≤ 21 := by
      calc
        a = a * 1 := by ring
        _ ≤ a * b := Nat.mul_le_mul_left a (Nat.succ_le_of_lt hb_pos)
        _ = 21 := hab
    have hsum : 10 ≤ a + b := by
      interval_cases a <;> omega
    omega
