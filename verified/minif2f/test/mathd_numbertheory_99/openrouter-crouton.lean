import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $2n \equiv 15 \pmod{47}$, as a residue modulo 47.  (Give an answer between 0 and 46.) -/
theorem mathd_numbertheory_99 (n : ℕ) (h₀ : 2 * n % 47 = 15) : n % 47 = 31 := by
  omega
