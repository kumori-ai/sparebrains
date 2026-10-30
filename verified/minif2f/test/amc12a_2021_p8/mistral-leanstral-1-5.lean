import Mathlib

open scoped Nat
open scoped Real

/--
A sequence of numbers is defined by $D_0=0,D_1=0,D_2=1$ and $D_n=D_{n-1}+D_{n-3}$ for $n\ge 3$. What are the parities (evenness or oddness) of the triple of numbers $(D_{2021},D_{2022},D_{2023})$, where $E$ denotes even and $O$ denotes odd?

$\textbf{(A) }(O,E,O) \qquad \textbf{(B) }(E,E,O) \qquad \textbf{(C) }(E,O,E) \qquad \textbf{(D) }(O,O,E) \qquad \textbf{(E) }(O,O,O)$ -/
theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  -- compute the first few terms
  have h3 : d 3 = 1 := by
    have h := h₃ 3 (by omega)
    rw [h]
    simp [h₂, h₀]
  have h4 : d 4 = 1 := by
    have h := h₃ 4 (by omega)
    rw [h]
    rw [h3, h₁]
  have h5 : d 5 = 2 := by
    have h := h₃ 5 (by omega)
    rw [h]
    rw [h4, h₂]
  have h6 : d 6 = 3 := by
    have h := h₃ 6 (by omega)
    rw [h]
    rw [h5, h3]
  have h7 : d 7 = 4 := by
    have h := h₃ 7 (by omega)
    rw [h]
    rw [h6, h4]
  have h8 : d 8 = 6 := by
    have h := h₃ 8 (by omega)
    rw [h]
    rw [h7, h5]
  have h9 : d 9 = 9 := by
    have h := h₃ 9 (by omega)
    rw [h]
    rw [h8, h6]
  -- prove that the sequence modulo 2 is periodic with period 7
  have h_period : ∀ n, d (n+7) % 2 = d n % 2 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n IH
    by_cases hn : n < 3
    · interval_cases n
      · -- n = 0
        rw [h₀, h7]
      · -- n = 1
        rw [h₁, h8]
      · -- n = 2
        rw [h₂, h9]
    · -- n ≥ 3
      have hn' : 3 ≤ n := by omega
      have h_eq : d n = d (n-1) + d (n-3) := h₃ n hn'
      have h_next : d (n+7) = d (n+6) + d (n+4) := by
        aesop
      rw [h_next]
      have IH1 := IH (n-1) (by omega)
      have IH3 := IH (n-3) (by omega)
      have h1 : (n:ℕ)-1+7 = n+6 := by omega
      have h3 : (n:ℕ)-3+7 = n+4 := by omega
      rw [h1] at IH1
      rw [h3] at IH3
      omega
  -- reduce 2021, 2022, 2023 modulo 7 using the periodicity
  have h2021 : d 2021 % 2 = 0 := by
    have h_mod : ∀ k : ℕ, d (5 + 7*k) % 2 = d 5 % 2 := by
      intro k
      induction' k with k IH
      · rfl
      · have : 5 + 7*(k+1) = (5 + 7*k) + 7 := by ring
        rw [this]
        rw [h_period]
        exact IH
    have h2021_eq : 2021 = 5 + 7*288 := by norm_num
    rw [h2021_eq]
    rw [h_mod 288]
    rw [h5]
  have h2022 : d 2022 % 2 = 1 := by
    have h_mod : ∀ k : ℕ, d (6 + 7*k) % 2 = d 6 % 2 := by
      intro k
      induction' k with k IH
      · rfl
      · have : 6 + 7*(k+1) = (6 + 7*k) + 7 := by ring
        rw [this]
        rw [h_period]
        exact IH
    have h2022_eq : 2022 = 6 + 7*288 := by norm_num
    rw [h2022_eq]
    rw [h_mod 288]
    rw [h6]
  have h2023 : d 2023 % 2 = 0 := by
    have h_mod : ∀ k : ℕ, d (0 + 7*k) % 2 = d 0 % 2 := by
      intro k
      induction' k with k IH
      · rfl
      · have : 0 + 7*(k+1) = (0 + 7*k) + 7 := by ring
        rw [this]
        rw [h_period]
        exact IH
    have h2023_eq : 2023 = 0 + 7*289 := by norm_num
    rw [h2023_eq]
    rw [h_mod 289]
    rw [h₀]
  -- convert the modular equalities to Even/Odd statements
  have h_even_2021 : Even (d 2021) := by
    have := Nat.div_add_mod (d 2021) 2
    rw [h2021, add_zero] at this
    refine ⟨d 2021 / 2, ?_⟩
    omega
  have h_odd_2022 : Odd (d 2022) := by
    have := Nat.div_add_mod (d 2022) 2
    rw [h2022] at this
    refine ⟨d 2022 / 2, ?_⟩
    omega
  have h_even_2023 : Even (d 2023) := by
    have := Nat.div_add_mod (d 2023) 2
    rw [h2023, add_zero] at this
    refine ⟨d 2023 / 2, ?_⟩
    omega
  exact And.intro h_even_2021 (And.intro h_odd_2022 h_even_2023)
