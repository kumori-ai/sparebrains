import Mathlib

open scoped Nat
open scoped Real

/--
Prove that the fraction $ \dfrac{21n +{} 4}{14n +{} 3}$ is irreducible for every natural number $ n$. -/
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (21 * (n : ℤ) + 4) := by
    exact_mod_cast Nat.gcd_dvd_left _ _
  have h2 : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (14 * (n : ℤ) + 3) := by
    exact_mod_cast Nat.gcd_dvd_right _ _
  have h3 : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣
      3 * (14 * (n : ℤ) + 3) - 2 * (21 * (n : ℤ) + 4) :=
    dvd_sub (h2.mul_left 3) (h1.mul_left 2)
  have h4 : 3 * (14 * (n : ℤ) + 3) - 2 * (21 * (n : ℤ) + 4) = 1 := by ring
  rw [h4] at h3
  have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by exact_mod_cast h3
  exact Nat.dvd_one.mp h5
