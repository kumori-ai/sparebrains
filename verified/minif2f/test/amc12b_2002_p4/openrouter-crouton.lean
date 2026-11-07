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
  set q : ℚ := (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n with hq_def
  have hq : q = (q.num : ℚ) := by
    have h := Rat.num_div_den q
    rw [h₁] at h
    simpa using h.symm
  have hsum : (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 = 41 / 42 := by norm_num
  have hq2 : q = 41 / 42 + 1 / (n : ℚ) := by
    rw [hq_def, hsum]
  have h_eq : (41 : ℚ) / 42 + 1 / (n : ℚ) = (q.num : ℚ) := by
    rw [← hq2]
    exact hq
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast h₀
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h₀
  have h1n_pos : (0 : ℚ) < 1 / (n : ℚ) := one_div_pos.mpr hnpos
  have h1n_le : 1 / (n : ℚ) ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hn1
    simpa using h
  have hnum_pos : (0 : ℚ) < (q.num : ℚ) := by linarith
  have hnum_lt : (q.num : ℚ) < 2 := by linarith
  have h0int : 0 < q.num := by exact_mod_cast hnum_pos
  have hnum_lt_int : q.num < 2 := by exact_mod_cast hnum_lt
  have hnum_eq : q.num = 1 := by omega
  have h1n : 1 / (n : ℚ) = 1 / 42 := by
    have hnum1 : (q.num : ℚ) = 1 := by exact_mod_cast hnum_eq
    linarith
  have hn42 : (n : ℚ) = 42 := by
    have h : (n : ℚ)⁻¹ = (42 : ℚ)⁻¹ := by simpa [one_div] using h1n
    exact inv_inj.mp h
  exact_mod_cast hn42
