import Mathlib

open scoped Nat
open scoped Real

/--
The first and ninth terms of an arithmetic sequence are $\frac23$ and $\frac45$, respectively. What is the fifth term? -/
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  set d := a 2 - a 1 with hd_def
  have hdiff : ∀ n, a (n + 1) - a n = d := by
    intro n
    induction' n with k ih
    · -- n = 0
      have h0 := h₀ 0
      rw [hd_def]
      linarith
    · -- n = k+1
      have hk := h₀ k
      rw [hd_def]
      linarith
  have h5sub1 : a 5 - a 1 = 4 * d := by
    calc
      a 5 - a 1 = (a 5 - a 4) + (a 4 - a 3) + (a 3 - a 2) + (a 2 - a 1) := by ring
      _ = d + d + d + d := by simp [hdiff]
      _ = 4 * d := by ring
  have h9sub5 : a 9 - a 5 = 4 * d := by
    calc
      a 9 - a 5 = (a 9 - a 8) + (a 8 - a 7) + (a 7 - a 6) + (a 6 - a 5) := by ring
      _ = d + d + d + d := by simp [hdiff]
      _ = 4 * d := by ring
  have h_eq : a 5 - a 1 = a 9 - a 5 := by rw [h5sub1, h9sub5]
  have h5_eq : 2 * a 5 = a 1 + a 9 := by linarith
  have h5_val : a 5 = (a 1 + a 9) / 2 := by
    field_simp
    simpa [mul_comm] using h5_eq
  calc
    a 5 = (a 1 + a 9) / 2 := h5_val
    _ = ((2 / 3 : ℝ) + (4 / 5 : ℝ)) / 2 := by rw [h₁, h₂]
    _ = 11 / 15 := by norm_num
