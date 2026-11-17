import Mathlib

open scoped Nat
open scoped Real

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ -/
theorem mathd_numbertheory_765 : IsGreatest {x : ℤ | x < 0 ∧ 24 * x % 1199 = 15} (-449) := by
  constructor
  · norm_num
  · intro x hx
    rcases hx with ⟨hxneg, hxmod⟩
    have hmod : Int.ModEq 1199 (24 * x) 15 := by
      change (24 * x) % 1199 = 15 % 1199
      rw [hxmod]
      norm_num
    have hdvd : (1199 : ℤ) ∣ 15 - 24 * x := (Int.modEq_iff_dvd.mp hmod)
    rcases hdvd with ⟨k, hk⟩
    have hx_eq : 750 - x = 1199 * (x + 50 * k) := by
      nlinarith
    have hdvd2 : (1199 : ℤ) ∣ 750 - x := ⟨x + 50 * k, hx_eq⟩
    rcases hdvd2 with ⟨m, hm⟩
    omega
