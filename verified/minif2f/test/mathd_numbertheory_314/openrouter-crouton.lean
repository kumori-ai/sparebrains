import Mathlib

open scoped Nat
open scoped Real

/-- Let $r$ be the remainder when $1342$ is divided by $13$.

Determine the smallest positive integer that has these two properties:

$\bullet~$ It is a multiple of $1342$.

$\bullet~$ Its remainder upon being divided by $13$ is smaller than $r$. -/
theorem mathd_numbertheory_314 (r : ℕ) (h₀ : r = 1342 % 13) :
    IsLeast {n : ℕ | 0 < n ∧ 1342 ∣ n ∧ n % 13 < r} 6710 := by
  have hr : r = 3 := by omega
  constructor
  · refine ⟨by norm_num, ⟨5, by norm_num⟩, ?_⟩
    rw [hr]
    norm_num
  · intro n hn
    obtain ⟨hnpos, hndvd, hnmod⟩ := hn
    obtain ⟨k, hk⟩ := hndvd
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        rw [h] at hk
        simp at hk
        omega
      · exact h
    have hk5 : 5 ≤ k := by
      by_contra hlt
      push_neg at hlt
      interval_cases k <;> rw [hk] at hnmod <;> rw [hr] at hnmod <;> norm_num at hnmod
    rw [hk]
    calc 6710 = 1342 * 5 := by norm_num
      _ ≤ 1342 * k := Nat.mul_le_mul_left 1342 hk5
