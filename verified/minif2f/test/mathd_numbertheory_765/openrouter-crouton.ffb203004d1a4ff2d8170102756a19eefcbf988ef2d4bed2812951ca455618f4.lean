import Mathlib

open scoped Nat
open scoped Real

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ -/
theorem mathd_numbertheory_765 : IsGreatest {x : ℤ | x < 0 ∧ 24 * x % 1199 = 15} (-449) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  intro x hx
  obtain ⟨hx_neg, hx_mod⟩ := hx
  have h0 : (24 * x - 15) % 1199 = 0 := by
    rw [Int.sub_emod, hx_mod]
    norm_num
  have hdvd : (1199 : ℤ) ∣ 24 * x - 15 := Int.dvd_of_emod_eq_zero h0
  obtain ⟨k, hk⟩ := hdvd
  omega
