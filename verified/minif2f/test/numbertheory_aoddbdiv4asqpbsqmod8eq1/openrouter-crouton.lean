import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  obtain ⟨k, hk⟩ := h₀
  obtain ⟨t, ht⟩ := h₁
  have hb : (b : ℤ) = 4 * (t : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) ht
    push_cast at h
    exact h
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hsum : a ^ 2 + (b : ℤ) ^ 2 = 8 * (2 * m ^ 2 + m + 2 * (t : ℤ) ^ 2) + 1 := by
      rw [hk, hm, hb]
      ring
    rw [hsum]
    omega
  · have hsum : a ^ 2 + (b : ℤ) ^ 2 = 8 * (2 * m ^ 2 + 3 * m + 1 + 2 * (t : ℤ) ^ 2) + 1 := by
      rw [hk, hm, hb]
      ring
    rw [hsum]
    omega
