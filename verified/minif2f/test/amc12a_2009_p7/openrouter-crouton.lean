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
  have hd : a 2 - a 1 = a 3 - a 2 := h₁ 1
  have hx : x = 4 := by
    rw [h₂, h₃, h₄] at hd
    linarith
  have ha1 : a 1 = 5 := by
    rw [h₂, hx]
    norm_num
  have hdval : a 2 - a 1 = 4 := by
    rw [h₃, h₂, hx]
    norm_num
  have key : ∀ m, a (m + 1) - a m = a 2 - a 1 := by
    intro m
    induction m with
    | zero =>
      have h := h₁ 0
      exact h
    | succ m ih =>
      have h := h₁ m
      have step : a (m + 2) - a (m + 1) = a 2 - a 1 := by linarith [h, ih]
      exact step
  have formula : ∀ k, a (k + 1) = a 1 + (k : ℝ) * (a 2 - a 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := key (k + 1)
      have step : a (k + 1 + 1) = a (k + 1) + (a 2 - a 1) := by linarith [hk]
      exact calc
        a (k + 1 + 1) = a (k + 1) + (a 2 - a 1) := step
        _ = (a 1 + (k : ℝ) * (a 2 - a 1)) + (a 2 - a 1) := by rw [ih]
        _ = a 1 + ((k + 1 : ℕ) : ℝ) * (a 2 - a 1) := by push_cast; ring
  rcases n with _ | k
  · have h' : a 1 - a 0 = a 2 - a 1 := key 0
    exfalso
    linarith [h', h₅, ha1, hdval]
  · have hf := formula k
    have hf' : a (k + 1) = 5 + (k : ℝ) * 4 := by rw [hf, hdval, ha1]
    have h5' : a (k + 1) = 2009 := h₅
    have hk_real : (k : ℝ) = 501 := by linarith [hf', h5']
    have hk_nat : k = 501 := by exact_mod_cast hk_real
    omega
