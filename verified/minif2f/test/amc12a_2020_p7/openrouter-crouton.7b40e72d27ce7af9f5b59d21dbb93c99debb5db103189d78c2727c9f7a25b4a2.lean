import Mathlib

open scoped Nat
open scoped Real

/--
Seven cubes, whose volumes are $1$, $8$, $27$, $64$, $125$, $216$, and $343$ cubic units, are stacked vertically to form a tower in which the volumes of the cubes decrease from bottom to top. Except for the bottom cube, the bottom face of each cube lies completely on top of the cube below it. What is the total surface area of the tower (including the bottom) in square units?

$\textbf{(A) } 644    \qquad \textbf{(B) } 658   \qquad \textbf{(C) } 664   \qquad \textbf{(D) } 720   \qquad \textbf{(E) } 749$ -/
theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    (↑(∑ k ∈ Finset.range 7, 6 * a k ^ 2 :) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2 :)) = (658 : ℤ) := by
  have ha0 : a 0 = 1 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 2 ≤ a 0 := by omega
      have h2 : (2 : ℕ) ^ 3 ≤ a 0 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₀] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 0 = 0 := by omega
      rw [h'] at h₀
      norm_num at h₀
  have ha1 : a 1 = 2 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 3 ≤ a 1 := by omega
      have h2 : (3 : ℕ) ^ 3 ≤ a 1 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₁] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 1 ≤ 1 := by omega
      have h2 : a 1 ^ 3 ≤ (1 : ℕ) ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₁] at h2
      norm_num at h2
  have ha2 : a 2 = 3 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 4 ≤ a 2 := by omega
      have h2 : (4 : ℕ) ^ 3 ≤ a 2 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₂] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 2 ≤ 2 := by omega
      have h2 : a 2 ^ 3 ≤ (2 : ℕ) ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₂] at h2
      norm_num at h2
  have ha3 : a 3 = 4 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 5 ≤ a 3 := by omega
      have h2 : (5 : ℕ) ^ 3 ≤ a 3 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₃] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 3 ≤ 3 := by omega
      have h2 : a 3 ^ 3 ≤ (3 : ℕ) ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₃] at h2
      norm_num at h2
  have ha4 : a 4 = 5 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 6 ≤ a 4 := by omega
      have h2 : (6 : ℕ) ^ 3 ≤ a 4 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₄] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 4 ≤ 4 := by omega
      have h2 : a 4 ^ 3 ≤ (4 : ℕ) ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₄] at h2
      norm_num at h2
  have ha5 : a 5 = 6 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 7 ≤ a 5 := by omega
      have h2 : (7 : ℕ) ^ 3 ≤ a 5 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₅] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 5 ≤ 5 := by omega
      have h2 : a 5 ^ 3 ≤ (5 : ℕ) ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₅] at h2
      norm_num at h2
  have ha6 : a 6 = 7 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have h' : 8 ≤ a 6 := by omega
      have h2 : (8 : ℕ) ^ 3 ≤ a 6 ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₆] at h2
      norm_num at h2
    · by_contra h
      push_neg at h
      have h' : a 6 ≤ 6 := by omega
      have h2 : a 6 ^ 3 ≤ (6 : ℕ) ^ 3 := Nat.pow_le_pow_left h' 3
      rw [h₆] at h2
      norm_num at h2
  norm_num [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6]
