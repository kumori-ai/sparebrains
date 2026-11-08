import Mathlib

open scoped Nat
open scoped Real

/--
A sequence of numbers is defined by $D_0=0,D_1=0,D_2=1$ and $D_n=D_{n-1}+D_{n-3}$ for $n\ge 3$. What are the parities (evenness or oddness) of the triple of numbers $(D_{2021},D_{2022},D_{2023})$, where $E$ denotes even and $O$ denotes odd?

$\textbf{(A) }(O,E,O) \qquad \textbf{(B) }(E,E,O) \qquad \textbf{(C) }(E,O,E) \qquad \textbf{(D) }(O,O,E) \qquad \textbf{(E) }(O,O,O)$ -/
theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  have hd3 : d 3 = 1 := by
    have h := h₃ 3 (by norm_num)
    rw [show 3 - 1 = 2 by norm_num, show 3 - 3 = 0 by norm_num, h₂, h₀] at h
    exact h
  have hd4 : d 4 = 1 := by
    have h := h₃ 4 (by norm_num)
    rw [show 4 - 1 = 3 by norm_num, show 4 - 3 = 1 by norm_num, hd3, h₁] at h
    exact h
  have hd5 : d 5 = 2 := by
    have h := h₃ 5 (by norm_num)
    rw [show 5 - 1 = 4 by norm_num, show 5 - 3 = 2 by norm_num, hd4, h₂] at h
    exact h
  have hd6 : d 6 = 3 := by
    have h := h₃ 6 (by norm_num)
    rw [show 6 - 1 = 5 by norm_num, show 6 - 3 = 3 by norm_num, hd5, hd3] at h
    exact h
  have hd7 : d 7 = 4 := by
    have h := h₃ 7 (by norm_num)
    rw [show 7 - 1 = 6 by norm_num, show 7 - 3 = 4 by norm_num, hd6, hd4] at h
    exact h
  have hd8 : d 8 = 6 := by
    have h := h₃ 8 (by norm_num)
    rw [show 8 - 1 = 7 by norm_num, show 8 - 3 = 5 by norm_num, hd7, hd5] at h
    exact h
  have hd9 : d 9 = 9 := by
    have h := h₃ 9 (by norm_num)
    rw [show 9 - 1 = 8 by norm_num, show 9 - 3 = 6 by norm_num, hd8, hd6] at h
    exact h
  have hd10 : d 10 = 13 := by
    have h := h₃ 10 (by norm_num)
    rw [show 10 - 1 = 9 by norm_num, show 10 - 3 = 7 by norm_num, hd9, hd7] at h
    exact h
  have hd11 : d 11 = 19 := by
    have h := h₃ 11 (by norm_num)
    rw [show 11 - 1 = 10 by norm_num, show 11 - 3 = 8 by norm_num, hd10, hd8] at h
    exact h
  have hd12 : d 12 = 28 := by
    have h := h₃ 12 (by norm_num)
    rw [show 12 - 1 = 11 by norm_num, show 12 - 3 = 9 by norm_num, hd11, hd9] at h
    exact h
  have hd13 : d 13 = 41 := by
    have h := h₃ 13 (by norm_num)
    rw [show 13 - 1 = 12 by norm_num, show 13 - 3 = 10 by norm_num, hd12, hd10] at h
    exact h
  have hper : ∀ n, d (n + 7) % 2 = d n % 2 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    by_cases hn : n < 7
    · interval_cases n <;>
        simp [h₀, h₁, h₂, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13]
    · have e1 := h₃ (n + 7) (by omega)
      rw [show n + 7 - 1 = n + 6 by omega, show n + 7 - 3 = n + 4 by omega] at e1
      have e2 := h₃ n (by omega)
      have ih1 := ih (n - 1) (by omega)
      rw [show n - 1 + 7 = n + 6 by omega] at ih1
      have ih2 := ih (n - 3) (by omega)
      rw [show n - 3 + 7 = n + 4 by omega] at ih2
      omega
  have hiter : ∀ k n, d (n + 7 * k) % 2 = d n % 2 := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have heq : n + 7 * (k + 1) = (n + 7 * k) + 7 := by ring
      rw [heq, hper (n + 7 * k), ih n]
  have h2021 : d 2021 % 2 = 0 := by
    have h := hiter 288 5
    rw [show 5 + 7 * 288 = 2021 by norm_num, hd5] at h
    exact h
  have h2022 : d 2022 % 2 = 1 := by
    have h := hiter 288 6
    rw [show 6 + 7 * 288 = 2022 by norm_num, hd6] at h
    exact h
  have h2023 : d 2023 % 2 = 0 := by
    have h := hiter 289 0
    rw [show 0 + 7 * 289 = 2023 by norm_num, h₀] at h
    exact h
  exact ⟨Nat.even_iff.mpr h2021, Nat.odd_iff.mpr h2022, Nat.even_iff.mpr h2023⟩
