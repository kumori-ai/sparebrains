import Mathlib

open scoped Nat
open scoped Real

/--
The greatest common divisor of positive integers $m$ and $n$ is 6. The least common multiple of $m$ and $n$ is 126. What is the least possible value of $m+n$? -/
theorem mathd_numbertheory_277 :
    IsLeast
       {(m + n) | (m : ℕ) (n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126)}
      60 := by
  refine ⟨⟨18, 42, by decide, by decide, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨m, n, hm, hn, rfl⟩ := hx
  have hm6 : 6 ∣ m := by
    rw [← hm]
    exact Nat.gcd_dvd_left m n
  have hn6 : 6 ∣ n := by
    rw [← hm]
    exact Nat.gcd_dvd_right m n
  obtain ⟨a, rfl⟩ := hm6
  obtain ⟨b, rfl⟩ := hn6
  have hprod : (6 * a) * (6 * b) = 756 := by
    have h := Nat.gcd_mul_lcm (6 * a) (6 * b)
    rw [hm, hn] at h
    omega
  have hab : a * b = 21 := by
    have h2 : (6 * a) * (6 * b) = 36 * (a * b) := by ring
    rw [h2] at hprod
    omega
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h] at hab
    · exact h
  have ha_le : a ≤ 21 := Nat.le_of_dvd (by norm_num) ⟨b, hab.symm⟩
  interval_cases a <;> omega
