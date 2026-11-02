import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) -/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by
  have hmod_lt : (3 * n) % 2 < 2 := Nat.mod_lt (3 * n) (by norm_num : 0 < 2)
  rw [h₀] at hmod_lt
  exact absurd hmod_lt (by norm_num : ¬ 11 < 2)
