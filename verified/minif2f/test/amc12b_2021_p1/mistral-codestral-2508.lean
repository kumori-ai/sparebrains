import Mathlib

open scoped Nat
open scoped Real

/-- How many integer values satisfy $|x|< 3\pi$?

$\textbf{(A) }9 \qquad \textbf{(B) }10 \qquad \textbf{(C) }18 \qquad \textbf{(D) }19 \qquad \textbf{(E) }20$ -/
theorem amc12b_2021_p1 (S : Finset ℤ) (h₀ : ∀ x : ℤ, x ∈ S ↔ ↑(abs x) < 3 * Real.pi) :
    S.card = 19 := by
  -- useful bounds on 3·π
  have h9_lt_3π : (9 : ℝ) < 3 * Real.pi := by
    calc
      (9 : ℝ) = (3 : ℝ) * 3 := by norm_num
      _ < (3 : ℝ) * Real.pi := by
        have : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
        exact mul_lt_mul_of_pos_left this (by norm_num)
  have h3π_lt_10 : (3 : ℝ) * Real.pi < 10 := by
    have hπ : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d6]
    have h1 : (3 : ℝ) * Real.pi < (3 : ℝ) * (22 / 7) :=
      mul_lt_mul_of_pos_left hπ (by norm_num)
    have h2 : (3 : ℝ) * (22 / 7) = (66 / 7 : ℝ) := by ring
    have h3 : (66 / 7 : ℝ) < 10 := by norm_num
    have : (3 : ℝ) * Real.pi < (66 / 7 : ℝ) := by
      simpa [h2] using h1
    exact lt_trans this h3
  -- equivalence between the predicate and a concrete interval
  have hmem : ∀ x : ℤ, x ∈ S ↔ -9 ≤ x ∧ x ≤ 9 := by
    intro x
    have hx : (x ∈ S) ↔ (↑|x| : ℝ) < 3 * Real.pi := h₀ x
    have : (↑|x| : ℝ) < 3 * Real.pi ↔ -9 ≤ x ∧ x ≤ 9 := by
      constructor
      · intro h
        have h10 : (↑|x| : ℝ) < (10 : ℝ) := lt_trans h h3π_lt_10
        have h_abs_lt_10 : |x| < (10 : ℤ) := by
          exact_mod_cast h10
        have h_abs_le_9 : |x| ≤ 9 :=
          (Int.lt_add_one_iff).mp (by
            simpa [add_comm] using h_abs_lt_10)
        exact (abs_le).mp h_abs_le_9
      · intro h
        have h_abs_le_9 : |x| ≤ 9 := (abs_le).mpr h
        have h_abs_lt_3π : (↑|x| : ℝ) < 3 * Real.pi := by
          have : (↑|x| : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h_abs_le_9
          exact lt_of_le_of_lt this h9_lt_3π
        exact h_abs_lt_3π
    exact hx.trans this
  have hS : S = Finset.Icc (-9) 9 := by
    ext x
    simpa [Finset.mem_Icc] using hmem x
  have hcard : (Finset.Icc (-9) 9).card = 19 := by
    decide
  simpa [hS] using hcard
