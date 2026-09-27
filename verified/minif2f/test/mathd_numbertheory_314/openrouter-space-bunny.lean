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
    norm_num [h₀]
  refine ⟨⟨by norm_num, ?_, ?_⟩, ?_⟩
  · exact ⟨5, by norm_num⟩
  · norm_num [hr]
  · intro n hn
    rcases hn with ⟨hnpos, hndiv, hnmod⟩
    rcases hndiv with ⟨k, rfl⟩
    have hkpos : 0 < k := by
      have h1342pos : 0 < 1342 := by norm_num
      omega
    by_cases hk5 : 5 ≤ k
    · omega
    · have hklt5 : k < 5 := by omega
      interval_cases k <;> norm_num [hr] at hnpos hnmod
