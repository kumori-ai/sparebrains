import Mathlib

open scoped Nat
open scoped Real

/-- Let $r$ be the remainder when $1342$ is divided by $13$.

Determine the smallest positive integer that has these two properties:

$\bullet~$ It is a multiple of $1342$.

$\bullet~$ Its remainder upon being divided by $13$ is smaller than $r$. -/
theorem mathd_numbertheory_314 (r : ℕ) (h₀ : r = 1342 % 13) :
    IsLeast {n : ℕ | 0 < n ∧ 1342 ∣ n ∧ n % 13 < r} 6710 := by
  have hr : r = 3 := by
    rw [h₀]
  refine ⟨⟨by norm_num, ⟨5, by norm_num⟩, by rw [hr]; norm_num⟩, ?_⟩
  intro n hn
  obtain ⟨hnpos, hdiv, hmod⟩ := hn
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk
      simp at hk
      omega
    · exact h
  have hk5 : 5 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k <;> rw [hk, hr] at hmod <;> norm_num at hmod
  calc
    6710 = 1342 * 5 := by norm_num
    _ ≤ 1342 * k := Nat.mul_le_mul le_rfl hk5
    _ = n := hk.symm
