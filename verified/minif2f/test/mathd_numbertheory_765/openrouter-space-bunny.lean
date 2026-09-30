import Mathlib

open scoped Nat
open scoped Real

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ -/
theorem mathd_numbertheory_765 : IsGreatest {x : ℤ | x < 0 ∧ 24 * x % 1199 = 15} (-449) := by
  constructor
  · norm_num
  · intro x hx
    have hx0 : x < 0 := hx.1
    have hmod : 24 * x % 1199 = 15 := hx.2
    by_contra hnot
    have hxrange : -449 ≤ x + 1 := by omega
    have hxupper : x ≤ -1 := by omega
    have hmul : -10776 ≤ 24*x ∧ 24*x ≤ -24 := by omega
    -- perhaps use `omega` on hmod
    omega
