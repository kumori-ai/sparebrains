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
    calc
      r = 1342 % 13 := h₀
      _ = 3 := by norm_num
  constructor
  · refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨5, by norm_num⟩
    · rw [hr]
      norm_num
  · intro n hn
    rcases hn with ⟨hpos, hdiv, hmod⟩
    rw [hr] at hmod
    rcases hdiv with ⟨k, hk⟩
    subst n
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      subst k
      norm_num at hpos
    have hkge : 5 ≤ k := by
      by_contra hklt
      have hklt' : k < 5 := by omega
      interval_cases k <;> norm_num at hmod
    calc
      6710 = 1342 * 5 := by norm_num
      _ ≤ 1342 * k := Nat.mul_le_mul_left 1342 hkge
