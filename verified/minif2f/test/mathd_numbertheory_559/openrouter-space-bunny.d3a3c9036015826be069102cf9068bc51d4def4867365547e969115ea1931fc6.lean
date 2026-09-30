import Mathlib

open scoped Nat
open scoped Real

/--
A positive integer $X$ is 2 more than a multiple of 3. Its units digit is the same as the units digit of a number that is 4 more than a multiple of 5. What is the smallest possible value of $X$? -/
theorem mathd_numbertheory_559 :
    IsLeast {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} 14 := by
  refine ⟨?_, ?_⟩
  · exact ⟨by norm_num, by norm_num, 4, by norm_num, by norm_num⟩
  · rintro x ⟨hx_pos, hx_mod₃, y, hy_mod₅, hx_mod₁₀⟩
    omega
