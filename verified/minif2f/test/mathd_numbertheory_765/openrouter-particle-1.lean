import Mathlib

open scoped Nat
open scoped Real

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ -/
theorem mathd_numbertheory_765 : IsGreatest {x : ℤ | x < 0 ∧ 24 * x % 1199 = 15} (-449) := by
  have key : ∀ x : ℤ, x < 0 → 24 * x % 1199 = 15 → x ≤ -449 := by
    intro x hxlt hmod
    have h15 : (15 : ℤ) % 1199 = 15 := by norm_num
    have hmod' : 24 * x % 1199 = 15 % 1199 := by
      rw [h15]
      exact hmod
    have hmodEq : (24 * x) ≡ 15 [ZMOD 1199] := by
      unfold Int.ModEq
      exact hmod'
    have hdiv : (1199 : ℤ) ∣ 24 * x - 15 := by
      first
      | exact (Int.modEq_iff_dvd).mp hmodEq
      | exact (Int.modEq_iff_dvd).mp hmodEq.symm
    have h1 : (1199 : ℤ) ∣ 50 * (24 * x - 15) := by
      simpa [mul_comm] using dvd_mul_of_dvd_left hdiv 50
    have h1' : (1199 : ℤ) ∣ 1199 * x + (x - 750) := by
      have heq : 50 * (24 * x - 15) = 1199 * x + (x - 750) := by ring
      rw [heq] at h1
      exact h1
    have h2 : (1199 : ℤ) ∣ 1199 * x := ⟨x, rfl⟩
    have h3 : (1199 : ℤ) ∣ x - 750 := by
      have hsub := dvd_sub h1' h2
      have heq : (1199 * x + (x - 750)) - 1199 * x = x - 750 := by ring
      rw [heq] at hsub
      exact hsub
    rcases h3 with ⟨k, hk⟩
    have hkneg : k < 0 := by
      by_contra hknonneg
      have hk0 : 0 ≤ k := by omega
      have hkpos : 0 ≤ 1199 * k := mul_nonneg (by norm_num) hk0
      nlinarith [hk, hkpos, hxlt]
    have hk_le : k ≤ -1 := by omega
    nlinarith [hk, hk_le]
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro x hx
    exact key x hx.1 hx.2
