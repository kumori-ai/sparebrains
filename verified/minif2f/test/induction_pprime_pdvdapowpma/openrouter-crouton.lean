import Mathlib

open scoped Nat
open scoped Real

theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  haveI : Fact p.Prime := ⟨h₁⟩
  have h : (a : ZMod p) ^ p = (a : ZMod p) := ZMod.pow_card _
  have hmod : a ^ p ≡ a [MOD p] := by
    have h2 : ((a ^ p : ℕ) : ZMod p) = ((a : ℕ) : ZMod p) := by
      push_cast
      exact h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  have hle : a ≤ a ^ p := by
    calc
      a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ p := pow_le_pow_right₀ h₀ h₁.one_lt.le
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm
