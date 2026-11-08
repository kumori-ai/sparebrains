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
      rw [h₀ n, ih]
      push_cast
      ring
  have hid98 : ∑ k ∈ Finset.range 98, (k : ℚ) = 4753 := by
    have h : (∑ i ∈ Finset.range 98, i) * 2 = 9506 := Finset.sum_range_id_mul_two 98
    have hc : ((∑ k ∈ Finset.range 98, k : ℕ) : ℚ) * 2 = 9506 := by exact_mod_cast h
    push_cast at hc
    linarith
  have hid49 : ∑ k ∈ Finset.range 49, (k : ℚ) = 1176 := by
    have h : (∑ i ∈ Finset.range 49, i) * 2 = 2352 := Finset.sum_range_id_mul_two 49
    have hc : ((∑ k ∈ Finset.range 49, k : ℕ) : ℚ) * 2 = 2352 := by exact_mod_cast h
    push_cast at hc
    linarith
  have hconst98 : ∑ k ∈ Finset.range 98, (1 : ℚ) = 98 := by simp
  have hconst49 : ∑ k ∈ Finset.range 49, (1 : ℚ) = 49 := by simp
  have hu0 : u 0 = -2357 / 49 := by
    have hsum : ∑ k ∈ Finset.range 98, u k.succ
        = ∑ k ∈ Finset.range 98, (u 0 + ((k : ℚ) + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hu k.succ]
      push_cast
      ring
    rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib] at h₁
    have hcu : ∑ k ∈ Finset.range 98, u 0 = 98 * u 0 := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcu, hid98, hconst98] at h₁
    linarith
  have hsum2 : ∑ k ∈ Finset.range 49, u (2 * k.succ)
      = ∑ k ∈ Finset.range 49, (u 0 + 2 * ((k : ℚ) + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hu (2 * k.succ)]
    push_cast
    ring
  rw [hsum2, Finset.sum_add_distrib]
  have h2 : ∑ k ∈ Finset.range 49, 2 * ((k : ℚ) + 1) = 2450 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hid49, hconst49]
    norm_num
  have hcu49 : ∑ k ∈ Finset.range 49, u 0 = 49 * u 0 := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hcu49, h2, hu0]
  norm_num
