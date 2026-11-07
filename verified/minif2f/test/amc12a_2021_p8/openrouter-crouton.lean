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
    simpa [h₀, h₂] using h
  have hd4 : d 4 = 1 := by
    have h := h₃ 4 (by norm_num)
    simpa [hd3, h₁] using h
  have hd5 : d 5 = 2 := by
    have h := h₃ 5 (by norm_num)
    simpa [hd4, h₂] using h
  have hd6 : d 6 = 3 := by
    have h := h₃ 6 (by norm_num)
    simpa [hd5, hd3] using h
  have hd7 : d 7 = 4 := by
    have h := h₃ 7 (by norm_num)
    simpa [hd6, hd4] using h
  have hd8 : d 8 = 6 := by
    have h := h₃ 8 (by norm_num)
    simpa [hd7, hd5] using h
  have hd9 : d 9 = 9 := by
    have h := h₃ 9 (by norm_num)
    simpa [hd8, hd6] using h
  have hper : ∀ n, d (n + 7) % 2 = d n % 2 := by
    have key : ∀ n, d (n + 7) % 2 = d n % 2 ∧ d (n + 8) % 2 = d (n + 1) % 2 ∧
        d (n + 9) % 2 = d (n + 2) % 2 := by
      intro n
      induction n with
      | zero =>
        refine ⟨?_, ?_, ?_⟩ <;> simp [hd7, hd8, hd9, h₀, h₁, h₂]
      | succ n ih =>
        obtain ⟨ih1, ih2, ih3⟩ := ih
        refine ⟨ih2, ih3, ?_⟩
        show d (n + 10) % 2 = d (n + 3) % 2
        have h10 : d (n + 10) = d (n + 9) + d (n + 7) := by
          have h := h₃ (n + 10) (by omega)
          rwa [show n + 10 - 1 = n + 9 by omega, show n + 10 - 3 = n + 7 by omega] at h
        have h3' : d (n + 3) = d (n + 2) + d n := by
          have h := h₃ (n + 3) (by omega)
          rwa [show n + 3 - 1 = n + 2 by omega, show n + 3 - 3 = n by omega] at h
        calc d (n + 10) % 2 = (d (n + 9) + d (n + 7)) % 2 := by rw [h10]
          _ = (d (n + 9) % 2 + d (n + 7) % 2) % 2 := by rw [Nat.add_mod]
          _ = (d (n + 2) % 2 + d n % 2) % 2 := by rw [ih3, ih1]
          _ = (d (n + 2) + d n) % 2 := (Nat.add_mod (d (n + 2)) (d n) 2).symm
          _ = d (n + 3) % 2 := by rw [h3']
    intro n
    exact (key n).1
  have hiter : ∀ k n, d (n + 7 * k) % 2 = d n % 2 := by
    intro k
    induction k with
    | zero =>
      intro n
      simp
    | succ k ih =>
      intro n
      rw [show n + 7 * (k + 1) = (n + 7 * k) + 7 by ring, hper (n + 7 * k), ih n]
  have e2021 : d 2021 % 2 = 0 := by
    have h := hiter 288 5
    rw [show 5 + 7 * 288 = 2021 by norm_num, hd5] at h
    simpa using h
  have e2022 : d 2022 % 2 = 1 := by
    have h := hiter 288 6
    rw [show 6 + 7 * 288 = 2022 by norm_num, hd6] at h
    simpa using h
  have e2023 : d 2023 % 2 = 0 := by
    have h := hiter 289 0
    rw [show 0 + 7 * 289 = 2023 by norm_num, h₀] at h
    simpa using h
  exact ⟨Nat.even_iff.mpr e2021, Nat.odd_iff.mpr e2022, Nat.even_iff.mpr e2023⟩
