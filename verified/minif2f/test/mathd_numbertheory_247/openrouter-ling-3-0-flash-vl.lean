import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) -/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by
  have h : 3 * n % 2 < 2 := Nat.mod_lt (3 * n) (Nat.zero_lt_two)
  have h₂ : 11 < 2 := by
    rw [h₀] at h
    exact h
  have h₃ : ¬(11 < 2) := Nat.not_lt_of_ge (by norm_num : 2 ≤ 11)
  exfalso
  exact h₃ h₂
