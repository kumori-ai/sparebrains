import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h1 : 1 - x ≤ abs (x - 1) := by
    have h := neg_le_abs (x - 1)
    linarith
  have h2 : x ≤ abs x := le_abs_self x
  have h3 : x + 1 ≤ abs (x + 1) := le_abs_self (x + 1)
  have e1 : abs (x - 1) = 1 - x := by linarith
  have e2 : abs x = x := by linarith
  constructor
  · have h := abs_nonneg x
    linarith
  · have h := abs_nonneg (x - 1)
    linarith
