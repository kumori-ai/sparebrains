import Mathlib

open scoped Nat
open scoped Real

/--
A positive integer $X$ is 2 more than a multiple of 3. Its units digit is the same as the units digit of a number that is 4 more than a multiple of 5. What is the smallest possible value of $X$? -/
theorem mathd_numbertheory_559 :
    IsLeast {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} 14 := by
  constructor
  · change
      0 < 14 ∧ 14 % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ 14 % 10 = y % 10
    constructor
    · norm_num
    · constructor
      · norm_num
      · exact ⟨4, by norm_num, by norm_num⟩
  · intro x hx
    change
      0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10 at hx
    rcases hx with ⟨hx0, hx3, y, hy5, hxy⟩
    omega
