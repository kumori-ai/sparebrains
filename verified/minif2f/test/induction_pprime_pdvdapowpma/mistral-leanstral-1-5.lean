import Mathlib

open scoped Nat
open scoped Real

theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  haveI : Fact p.Prime := ⟨h₁⟩
  have hp_one : 1 ≤ p := Nat.one_le_of_lt (Nat.Prime.one_lt h₁)
  have ha_one : 1 ≤ a := Nat.one_le_of_lt h₀
  have hle : a ≤ a ^ p := by
    exact Nat.le_pow hp_one
  have hzero : ((a ^ p - a : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hle, Nat.cast_pow]
    rw [ZMod.pow_card]
    simp
  exact (ZMod.natCast_eq_zero_iff (a ^ p - a) p).mp hzero