import Mathlib

open scoped Nat
open scoped Real

/--
A positive integer $X$ is 2 more than a multiple of 3. Its units digit is the same as the units digit of a number that is 4 more than a multiple of 5. What is the smallest possible value of $X$? -/
theorem mathd_numbertheory_559 :
    IsLeast {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} 14 := by
  constructor
  · refine ⟨by norm_num, by norm_num, ?_⟩
    exact ⟨14, by norm_num, by norm_num⟩
  · intro x hx
    rcases hx with ⟨hpos, hmod3, y, hy5, hmod10⟩
    have hy10 : y % 10 = 4 ∨ y % 10 = 9 := by
      set d := y % 10 with hd
      have hdlt : d < 10 := by
        rw [hd]
        exact Nat.mod_lt _ (by norm_num)
      have hdmod : d % 5 = 4 := by
        rw [hd]
        rw [Nat.mod_mod_of_dvd y (by norm_num : 5 ∣ 10)]
        exact hy5
      interval_cases d <;> norm_num at hdmod
      · left; omega
      · right; omega
    have hx10 : x % 10 = 4 ∨ x % 10 = 9 := by
      rcases hy10 with h | h
      · left; rw [hmod10, h]
      · right; rw [hmod10, h]
    rcases hx10 with hx10 | hx10
    · set q := x / 10 with hq
      set r := x / 3 with hr
      have hx_eq10 : x = 10 * q + 4 := by
        have hdiv := Nat.div_add_mod x 10
        rw [← hq] at hdiv
        omega
      have hx_eq3 : x = 3 * r + 2 := by
        have hdiv := Nat.div_add_mod x 3
        rw [← hr] at hdiv
        omega
      omega
    · set q := x / 10 with hq
      set r := x / 3 with hr
      have hx_eq10 : x = 10 * q + 9 := by
        have hdiv := Nat.div_add_mod x 10
        rw [← hq] at hdiv
        omega
      have hx_eq3 : x = 3 * r + 2 := by
        have hdiv := Nat.div_add_mod x 3
        rw [← hr] at hdiv
        omega
      omega
