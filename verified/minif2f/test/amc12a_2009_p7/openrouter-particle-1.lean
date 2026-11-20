import Mathlib

open scoped Nat
open scoped Real

/--
The first three terms of an arithmetic sequence are $ 2x-{}3$, $ 5x-{}11$, and $ 3x+{}1$ respectively. The $ n$th term of the sequence is $ 2009$. What is $ n$?

$ \textbf{(A)}\ 255 \qquad
\textbf{(B)}\ 502 \qquad
\textbf{(C)}\ 1004 \qquad
\textbf{(D)}\ 1506 \qquad
\textbf{(E)}\ 8037$ -/
theorem amc12a_2009_p7 (x : ℝ) (n : ℕ) (a : ℕ → ℝ)
    (h₁ : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1)) (h₂ : a 1 = 2 * x - 3)
    (h₃ : a 2 = 5 * x - 11) (h₄ : a 3 = 3 * x + 1) (h₅ : a n = 2009) : n = 502 := by
  have hx : x = 4 := by
    have h := h₁ 1
    norm_num at h
    rw [h₂, h₃, h₄] at h
    linarith
  have ha1 : a 1 = 5 := by
    rw [h₂, hx]
    norm_num
  have ha2 : a 2 = 9 := by
    rw [h₃, hx]
    norm_num
  have ha0 : a 0 = 1 := by
    have h := h₁ 0
    norm_num at h
    rw [ha1, ha2] at h
    linarith
  have hdiff : ∀ m : ℕ, a (m + 1) - a m = 4 := by
    intro m
    induction m with
    | zero =>
        have h := h₁ 0
        norm_num at h
        linarith [h, ha0, ha1, ha2]
    | succ k ih =>
        have h := h₁ k
        have h' : a (k + 2) - a (k + 1) = 4 := by
          linarith [h, ih]
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h'
  have hformula : ∀ k : ℕ, a k = 4 * (k : ℝ) + 1 := by
    intro k
    induction k with
    | zero =>
        simpa using ha0
    | succ k ih =>
        have hd := hdiff k
        calc
          a (k + 1) = a k + 4 := by linarith
          _ = (4 * (k : ℝ) + 1) + 4 := by rw [ih]
          _ = 4 * ((k + 1 : ℕ) : ℝ) + 1 := by
            push_cast
            ring
  have hnreal : (n : ℝ) = 502 := by
    have hn : 4 * (n : ℝ) + 1 = 2009 := by
      calc
        4 * (n : ℝ) + 1 = a n := (hformula n).symm
        _ = 2009 := h₅
    linarith
  exact_mod_cast hnreal
