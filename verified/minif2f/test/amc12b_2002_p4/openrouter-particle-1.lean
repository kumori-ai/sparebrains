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
  let q : ℚ := (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n
  have hqden : q.den = 1 := by
    simpa [q] using h₁
  have hqint : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp hqden
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast h₀
  have hpos : (0 : ℚ) < (1 : ℚ) / ↑n := by
    exact div_pos zero_lt_one hnpos
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt h₀)
  have hle : (1 : ℚ) / ↑n ≤ 1 := by
    rw [div_le_iff₀ hnpos]
    simpa using hn1
  have hq_gt : (41 : ℚ) / 42 < (q.num : ℚ) := by
    rw [hqint]
    dsimp [q]
    calc
      (41 : ℚ) / 42 < (41 : ℚ) / 42 + (1 : ℚ) / ↑n := by linarith [hpos]
      _ = (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n := by norm_num
  have hq_lt : (q.num : ℚ) < 2 := by
    rw [hqint]
    dsimp [q]
    calc
      (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n
          = (41 : ℚ) / 42 + (1 : ℚ) / ↑n := by norm_num
      _ ≤ (41 : ℚ) / 42 + 1 := by linarith [hle]
      _ < 2 := by norm_num
  have hz_ge : (1 : ℤ) ≤ q.num := by
    by_contra h
    have hzle : q.num ≤ 0 := by omega
    have hzle' : (q.num : ℚ) ≤ 0 := by exact_mod_cast hzle
    have hpos41 : (0 : ℚ) < (41 : ℚ) / 42 := by norm_num
    linarith
  have hz_le : q.num ≤ 1 := by
    by_contra h
    have hzge : 2 ≤ q.num := by omega
    have hzge' : (2 : ℚ) ≤ (q.num : ℚ) := by exact_mod_cast hzge
    linarith
  have hz_eq : q.num = 1 := by omega
  have hq1 : q = 1 := by
    rw [← hqint, hz_eq]
    norm_num
  have hqeq : (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 + (1 : ℚ) / ↑n = 1 := by
    simpa [q] using hq1
  have hsum : (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 7 = (41 : ℚ) / 42 := by
    norm_num
  have h_inv : (1 : ℚ) / ↑n = (1 : ℚ) / 42 := by
    linarith [hqeq, hsum]
  have hnq : (n : ℚ) = 42 := by
    have hnne : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt h₀)
    field_simp [hnne] at h_inv
    linarith
  exact_mod_cast hnq
