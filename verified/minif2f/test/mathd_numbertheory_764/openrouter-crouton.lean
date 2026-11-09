import Mathlib

open scoped Nat
open scoped Real

/--
Given that $p\ge 7$ is a prime number, evaluate $$1^{-1} \cdot 2^{-1} + 2^{-1} \cdot 3^{-1} + 3^{-1} \cdot 4^{-1} + \cdots + (p-2)^{-1} \cdot (p-1)^{-1} \pmod{p}.$$ -/
theorem mathd_numbertheory_764 (p : ℕ) (h₀ : Nat.Prime p) (h₁ : 7 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 2), (k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹ = 2 := by
  haveI : Fact p.Prime := ⟨h₀⟩
  have hp_pos : 0 < p := h₀.pos
  have hIcc : Finset.Icc 1 (p - 2) = Finset.Ico 1 (p - 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc]
  have key : ∀ k ∈ Finset.Ico 1 (p - 1),
      (k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹ =
        (-(((k + 1 : ℕ) : ZMod p)⁻¹) - (-(k : ZMod p)⁻¹)) := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hk_ne : (k : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ k := (CharP.cast_eq_zero_iff (ZMod p) p k).mp h
      have hle : p ≤ k := Nat.le_of_dvd (by omega) hdvd
      omega
    have hk1_ne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ k + 1 := (CharP.cast_eq_zero_iff (ZMod p) p (k + 1)).mp h
      have hle : p ≤ k + 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    have hcast : ((k + 1 : ℕ) : ZMod p) = (k : ZMod p) + 1 := by push_cast; ring
    have ha1 : (k : ZMod p) + 1 ≠ 0 := by
      rw [← hcast]; exact hk1_ne
    rw [hcast]
    field_simp [hk_ne, ha1]
    ring
  have hsum := Finset.sum_congr rfl key
  rw [hsum]
  have tele : ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Ico 1 n, (-(((k + 1 : ℕ) : ZMod p)⁻¹) - (-(k : ZMod p)⁻¹)) =
        -(((n : ℕ) : ZMod p)⁻¹) - (-(((1 : ℕ) : ZMod p)⁻¹)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro h
      by_cases hn : n = 0
      · subst hn; simp
      · have hn1 : 1 ≤ n := by omega
        rw [Finset.sum_Ico_succ_top hn1, ih hn1]
        ring
  rw [tele (p - 1) (show 1 ≤ p - 1 by omega)]
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
    simp
  rw [hcast]
  have hneg : (-1 : ZMod p)⁻¹ = -1 := by rw [inv_neg, inv_one]
  rw [hneg]
  simp only [Nat.cast_one, inv_one]
  ring
