import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) -/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by
  have h₁ : 3 * n % 2 = 0 ∨ 3 * n % 2 = 1 := Nat.mod_two_eq_zero_or_one (3 * n)
  cases h₁ with
  | inl h₁ =>
    rw [h₁] at h₀
    omega
  | inr h₁ =>
    rw [h₁] at h₀
    omega
