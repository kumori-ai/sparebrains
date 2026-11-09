import Mathlib

open scoped Nat
open scoped Real

/--
Seven cubes, whose volumes are $1$, $8$, $27$, $64$, $125$, $216$, and $343$ cubic units, are stacked vertically to form a tower in which the volumes of the cubes decrease from bottom to top. Except for the bottom cube, the bottom face of each cube lies completely on top of the cube below it. What is the total surface area of the tower (including the bottom) in square units?

$\textbf{(A) } 644    \qquad \textbf{(B) } 658   \qquad \textbf{(C) } 664   \qquad \textbf{(D) } 720   \qquad \textbf{(E) } 749$ -/
theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    (↑(∑ k ∈ Finset.range 7, 6 * a k ^ 2 :) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2 :)) = (658 : ℤ) := by
  have key : ∀ x k : ℕ, x ^ 3 = k ^ 3 → x = k := by
    intro x k h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (x + 1) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 : (x + 1) ^ 3 = x ^ 3 + (3 * x ^ 2 + 3 * x + 1) := by ring
      omega
    · have h1 : (k + 1) ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hgt 3
      have h2 : (k + 1) ^ 3 = k ^ 3 + (3 * k ^ 2 + 3 * k + 1) := by ring
      omega
  have ha0 : a 0 = 1 := key _ _ (by simpa using h₀)
  have ha1 : a 1 = 2 := key _ _ (by simpa using h₁)
  have ha2 : a 2 = 3 := key _ _ (by simpa using h₂)
  have ha3 : a 3 = 4 := key _ _ (by simpa using h₃)
  have ha4 : a 4 = 5 := key _ _ (by simpa using h₄)
  have ha5 : a 5 = 6 := key _ _ (by simpa using h₅)
  have ha6 : a 6 = 7 := key _ _ (by simpa using h₆)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, ha0, ha1, ha2, ha3, ha4, ha5, ha6]
