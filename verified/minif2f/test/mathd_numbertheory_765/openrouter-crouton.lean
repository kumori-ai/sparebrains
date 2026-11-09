import Mathlib

open scoped Nat
open scoped Real

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ -/
theorem mathd_numbertheory_765 : IsGreatest {x : ℤ | x < 0 ∧ 24 * x % 1199 = 15} (-449) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  omega
