import Mathlib

open scoped Nat
open scoped Real

/--
How many $4$-digit positive integers (that is, integers between $1000$ and $9999$, inclusive) having only even digits are divisible by $5?$

$\textbf{(A) } 80 \qquad \textbf{(B) } 100 \qquad \textbf{(C) } 125 \qquad \textbf{(D) } 200 \qquad \textbf{(E) } 500$ -/
theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by
  have h_even_iff : ∀ n : ℕ, (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ↔ (∀ d ∈ Nat.digits 10 n, d % 2 = 0) := by
    intro n
    constructor
    · intro h d hd
      rcases h d hd with ⟨k, hk⟩
      rw [hk]
      omega
    · intro h d hd
      have hmod := h d hd
      grind
  have hS_eq : S = (Finset.Icc 1000 9999).filter (λ n => (∀ d ∈ Nat.digits 10 n, d % 2 = 0) ∧ 5 ∣ n) := by
    ext n
    rw [h₀ n]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      aesop
    · aesop
  rw [hS_eq]
  set_option maxRecDepth 1000000 in
  decide
