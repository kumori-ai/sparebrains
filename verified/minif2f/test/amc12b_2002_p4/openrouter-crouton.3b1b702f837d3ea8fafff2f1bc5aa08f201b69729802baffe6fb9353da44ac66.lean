import Mathlib

open scoped Nat
open scoped Real

/--
Let $ n$ be a positive integer such that $ \tfrac{1}{2}+{}\tfrac{1}{3}+{}\tfrac{1}{7}+{}\tfrac{1}{n}$ is an integer. Which of the following statements is [b]not[/b] true?

$ \textbf{(A)}\ 2\text{ divides }n \qquad
\textbf{(B)}\ 3\text{ divides }n \qquad
\textbf{(C)}\ 6\text{ divides }n \qquad
\textbf{(D)}\ 7\text{ divides }n \\
\textbf{(E)}\ n>84$ -/
theorem amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) (h₁ : ((1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n).den = 1) :
    n = 42 := by
  have hn : (0 : ℚ) < n := by exact_mod_cast h₀
  have hsum : (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 = 41 / 42 := by norm_num
  set S : ℚ := (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n with hS_def
  have hS_eq : S = 41 / 42 + 1 / (n : ℚ) := by
    rw [hS_def, hsum]
  have hS_pos : 0 < S := by
    rw [hS_eq]
    have hpos : 0 < (1 : ℚ) / (n : ℚ) := one_div_pos.mpr hn
    linarith
  have hS_lt : S < 2 := by
    rw [hS_eq]
    have h1 : (1 : ℚ) / (n : ℚ) ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast h₀)
    linarith
  have hnum_eq : S = (S.num : ℚ) := by
    calc S = (S.num : ℚ) / (S.den : ℚ) := (Rat.num_div_den S).symm
      _ = (S.num : ℚ) := by rw [h₁]; simp
  have hnum_pos : 0 < S.num := by
    have h : (0 : ℚ) < (S.num : ℚ) := by rw [← hnum_eq]; exact hS_pos
    exact_mod_cast h
  have hnum_lt : S.num < 2 := by
    have h : (S.num : ℚ) < (2 : ℚ) := by rw [← hnum_eq]; exact hS_lt
    exact_mod_cast h
  have hnum_one : S.num = 1 := by omega
  have hS_one : S = 1 := by rw [hnum_eq, hnum_one]; norm_num
  have h_inv : (1 : ℚ) / (n : ℚ) = 1 / 42 := by
    rw [hS_eq] at hS_one
    linarith
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn
  have h42_ne : (42 : ℚ) ≠ 0 := by norm_num
  rw [div_eq_div_iff hn_ne h42_ne] at h_inv
  have hcast : (n : ℚ) = 42 := by linarith
  exact_mod_cast hcast
