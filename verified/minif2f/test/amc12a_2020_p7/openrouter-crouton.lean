import Mathlib

open scoped Nat
open scoped Real

/--
Seven cubes, whose volumes are $1$, $8$, $27$, $64$, $125$, $216$, and $343$ cubic units, are stacked vertically to form a tower in which the volumes of the cubes decrease from bottom to top. Except for the bottom cube, the bottom face of each cube lies completely on top of the cube below it. What is the total surface area of the tower (including the bottom) in square units?

$\textbf{(A) } 644    \qquad \textbf{(B) } 658   \qquad \textbf{(C) } 664   \qquad \textbf{(D) } 720   \qquad \textbf{(E) } 749$ -/
theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    (↑(∑ k ∈ Finset.range 7, 6 * a k ^ 2 :) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2 :)) = (658 : ℤ) := by
  have key : ∀ (x n : ℕ), 0 < n → x ^ 3 = n ^ 3 → x = n := by
    intro x n hn h
    have hz : (x : ℤ) ^ 3 = (n : ℤ) ^ 3 := by exact_mod_cast h
    have hfact : ((x : ℤ) - (n : ℤ)) * ((x : ℤ) ^ 2 + (x : ℤ) * (n : ℤ) + (n : ℤ) ^ 2) = 0 := by
      linear_combination hz
    rcases mul_eq_zero.mp hfact with h1 | h2
    · have hxz : (x : ℤ) = (n : ℤ) := by linarith
      exact_mod_cast hxz
    · have hx : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
      have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
      have hpos : (0 : ℤ) < (x : ℤ) ^ 2 + (x : ℤ) * (n : ℤ) + (n : ℤ) ^ 2 := by
        nlinarith [sq_nonneg (x : ℤ), mul_nonneg hx hn'.le, mul_pos hn' hn']
      exfalso
      linarith
  have ha0 : a 0 = 1 := key (a 0) 1 (by norm_num) (by simpa using h₀)
  have ha1 : a 1 = 2 := key (a 1) 2 (by norm_num) (by simpa using h₁)
  have ha2 : a 2 = 3 := key (a 2) 3 (by norm_num) (by simpa using h₂)
  have ha3 : a 3 = 4 := key (a 3) 4 (by norm_num) (by simpa using h₃)
  have ha4 : a 4 = 5 := key (a 4) 5 (by norm_num) (by simpa using h₄)
  have ha5 : a 5 = 6 := key (a 5) 6 (by norm_num) (by simpa using h₅)
  have ha6 : a 6 = 7 := key (a 6) 7 (by norm_num) (by simpa using h₆)
  have hsum7 : (∑ k ∈ Finset.range 7, 6 * a k ^ 2) = 840 := by
    norm_num [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6]
  have hsum6 : (∑ k ∈ Finset.range 6, a k ^ 2) = 91 := by
    norm_num [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5]
  rw [hsum7, hsum6]
  norm_num
