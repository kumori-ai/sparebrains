import Mathlib

open scoped Nat
open scoped Real

/--
Find the value of $a_2 + a_4 + a_6 + \dots + a_{98}$ if $a_1$, $a_2$, $a_3$, $\dots$ is an arithmetic progression with common difference 1, and $a_1 + a_2 + a_3 + \dots + a_{98} = 137$. -/
theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : ∑ k ∈ Finset.range 98, u k.succ = 137) : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
  have hu : ∀ n : ℕ, u n = u 0 + (n : ℚ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      show u (n + 1) = u 0 + ((n + 1 : ℕ) : ℚ)
      rw [h₀ n, ih]
      push_cast
      ring
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, (u 0 + (k : ℚ)) = (n : ℚ) * u 0 + (n : ℚ) * ((n : ℚ) - 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsum2 : ∀ n : ℕ, ∑ k ∈ Finset.range n, (u 0 + 2 * ((k : ℚ) + 1)) = (n : ℚ) * u 0 + (n : ℚ) * ((n : ℚ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hterm : ∀ k ∈ Finset.range 98, u k.succ = (u 0 + (k : ℚ)) + 1 := by
    intro k _
    show u (k + 1) = (u 0 + (k : ℚ)) + 1
    rw [hu]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hsum 98] at h₁
  simp at h₁
  norm_num at h₁
  have hterm2 : ∀ k ∈ Finset.range 49, u (2 * k.succ) = u 0 + 2 * ((k : ℚ) + 1) := by
    intro k _
    show u (2 * (k + 1)) = u 0 + 2 * ((k : ℚ) + 1)
    rw [hu]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm2, hsum2 49]
  norm_num
  linarith
