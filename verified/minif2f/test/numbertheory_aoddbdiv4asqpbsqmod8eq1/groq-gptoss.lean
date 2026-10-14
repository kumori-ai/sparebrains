import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  rcases h₀ with ⟨k, hk⟩
  rcases h₁ with ⟨m, hm⟩
  have h_a : a ^ 2 = 4 * k * (k + 1) + 1 := by
    rw [hk]
    ring
  have h_b : (b : ℤ) ^ 2 = 16 * (m : ℤ) ^ 2 := by
    rw [hm]
    norm_cast
    ring
  have h_mod_inner : (4 * k * (k + 1) + 1 + 16 * (m : ℤ) ^ 2) % 8 = 1 := by
    have h_even : Even (k * (k + 1)) := by
      rcases Int.even_or_odd k with hk_even | hk_odd
      · rcases hk_even with ⟨t, rfl⟩
        refine ⟨t * (2 * t + 1), ?_⟩
        ring
      · rcases hk_odd with ⟨t, rfl⟩
        refine ⟨(2 * t + 1) * (t + 1), ?_⟩
        ring
    rcases h_even with ⟨n, hn⟩
    have h_mul8 : 4 * k * (k + 1) = 8 * n := by
      calc
        4 * k * (k + 1) = (4 : ℤ) * (k * (k + 1)) := by ring
        _ = (4 : ℤ) * (2 * n) := by
          omega
        _ = 8 * n := by ring
    have : (8 * n + 1 + 16 * (m : ℤ) ^ 2) % 8 = 1 := by
      omega
    simpa [h_mul8] using this
  simpa [h_a, h_b] using h_mod_inner
