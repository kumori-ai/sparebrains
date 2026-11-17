import Mathlib

open scoped Nat
open scoped Real

/--
Prove that the fraction $ \dfrac{21n +{} 4}{14n +{} 3}$ is irreducible for every natural number $ n$. -/
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 21 * n + 4 :=
    Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 14 * n + 3 :=
    Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 3 * (14 * n + 3) :=
    dvd_mul_of_dvd_right h2 3
  have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 2 * (21 * n + 4) :=
    dvd_mul_of_dvd_right h1 2
  have heq : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by
    ring
  have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 2 * (21 * n + 4) + 1 := by
    rw [← heq]
    exact h3
  have h6 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣
      (2 * (21 * n + 4) + 1) - 2 * (21 * n + 4) :=
    Nat.dvd_sub h5 h4
  have hsub : (2 * (21 * n + 4) + 1) - 2 * (21 * n + 4) = 1 := by
    omega
  have hd : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
    simpa [hsub] using h6
  exact Nat.dvd_one.mp hd
