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
  have h : a 2 - a 1 = a 3 - a 2 := h₁ 1
  rw [h₂, h₃, h₄] at h
  have hx : x = 4 := by linarith
  have ha1 : a 1 = 5 := by rw [h₂, hx]; norm_num
  have ha2 : a 2 = 9 := by rw [h₃, hx]; norm_num
  have hdiff : ∀ m : ℕ, a (m + 1) - a m = 4 := by
    intro m
    induction m with
    | zero =>
      have h0 : a 1 - a 0 = a 2 - a 1 := h₁ 0
      show a 1 - a 0 = 4
      linarith
    | succ m ih =>
      have h1m : a (m + 1) - a m = a (m + 1 + 1) - a (m + 1) := h₁ m
      show a (m + 1 + 1) - a (m + 1) = 4
      linarith
  have hform : ∀ m : ℕ, a (m + 1) = 5 + (m : ℝ) * 4 := by
    intro m
    induction m with
    | zero => simpa using ha1
    | succ m ih =>
      have hd := hdiff (m + 1)
      show a (m + 1 + 1) = 5 + ((m + 1 : ℕ) : ℝ) * 4
      push_cast
      linarith
  cases n with
  | zero =>
    have hd0 : a 1 - a 0 = 4 := hdiff 0
    rw [ha1, h₅] at hd0
    norm_num at hd0
  | succ k =>
    have hf := hform k
    have h5' : a (k + 1) = 2009 := h₅
    have hk : (k : ℝ) = 501 := by linarith
    have hkNat : k = 501 := by exact_mod_cast hk
    omega
