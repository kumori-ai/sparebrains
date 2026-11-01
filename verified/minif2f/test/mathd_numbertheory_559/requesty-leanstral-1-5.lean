import Mathlib

open scoped Nat
open scoped Real

/--
A positive integer $X$ is 2 more than a multiple of 3. Its units digit is the same as the units digit of a number that is 4 more than a multiple of 5. What is the smallest possible value of $X$? -/
theorem mathd_numbertheory_559 :
    IsLeast {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} 14 := by
  constructor
  · -- 14 is in the set
    refine ⟨by norm_num, ?_, ?_⟩
    · norm_num
    · refine ⟨4, ?_, ?_⟩
      · norm_num
      · norm_num
  · -- for all b in the set, 14 ≤ b
    intro b hb
    rcases hb with ⟨hbpos, hbmod3, y, hy, hxy⟩
    have h_cases : b % 10 = 4 ∨ b % 10 = 9 := by
      have hy_mod10 : y % 10 = 4 ∨ y % 10 = 9 := by
        set r := y % 10 with hr
        set q := y / 10 with hq
        have hy_eq : y = 10 * q + r := by
          rw [hq, hr, Nat.div_add_mod y 10]
        have hr_lt : r < 10 := Nat.mod_lt y (by norm_num)
        have h_mod5 : r % 5 = 4 := by
          calc
            r % 5 = (y % 10) % 5 := by rfl
            _ = y % 5 := by rw [Nat.mod_mod_of_dvd y (show 5 ∣ 10 from by norm_num)]
            _ = 4 := hy
        omega
      rcases hy_mod10 with (h | h)
      · left; rw [hxy, h]
      · right; rw [hxy, h]
    by_cases hb_lt_14 : b < 14
    · have h_empty : ((Finset.range 14).filter (λ x => 0 < x ∧ x % 3 = 2 ∧ (x % 10 = 4 ∨ x % 10 = 9))) = ∅ := by
        decide
      have hmem : b ∈ (Finset.range 14).filter (λ x => 0 < x ∧ x % 3 = 2 ∧ (x % 10 = 4 ∨ x % 10 = 9)) := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr hb_lt_14, hbpos, hbmod3, h_cases⟩
      rw [h_empty] at hmem
      simp at hmem
    · exact Nat.le_of_not_lt hb_lt_14
