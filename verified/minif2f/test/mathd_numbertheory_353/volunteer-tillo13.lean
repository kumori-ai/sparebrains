import Mathlib

open scoped Nat
open scoped Real

/-- Let $S = 2010 + 2011 + \cdots + 4018$. Compute the residue of $S$, modulo 2009. -/
theorem mathd_numbertheory_353 (s : ℕ) (h₀ : s = ∑ k ∈ Finset.Icc 2010 4018, k) : s % 2009 = 0 := by
  subst s
  set_option maxRecDepth 100000 in
    decide +kernel
