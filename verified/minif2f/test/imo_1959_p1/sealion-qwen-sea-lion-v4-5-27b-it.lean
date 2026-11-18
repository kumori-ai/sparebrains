import Mathlib

open scoped Nat
open scoped Real

/--
Prove that the fraction $ \dfrac{21n +{} 4}{14n +{} 3}$ is irreducible for every natural number $ n$. -/
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h₂ : 3 * (14 * n + 3) - 2 * (21 * n + 4) = 1 := by omega
  have h₃ : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
    have h₄ : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4) := Nat.gcd_dvd_left _ _
    have h₅ : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3) := Nat.gcd_dvd_right _ _
    have h₆ : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 2 * (21 * n + 4) := dvd_mul_of_dvd_right h₄ 2
    have h₇ : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 3 * (14 * n + 3) := dvd_mul_of_dvd_right h₅ 3
    have h₈ : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 3 * (14 * n + 3) - 2 * (21 * n + 4) := Nat.dvd_sub h₇ h₆
    rw [h₂] at h₈
    exact h₈
  exact Nat.dvd_one.mp h₃
