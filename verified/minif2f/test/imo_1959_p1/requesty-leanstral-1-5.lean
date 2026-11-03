import Mathlib

open scoped Nat
open scoped Real

/--
Prove that the fraction $ \dfrac{21n +{} 4}{14n +{} 3}$ is irreducible for every natural number $ n$. -/
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have hcomb : ((3 : ℤ) * (14 * n + 3 : ℤ) - (2 : ℤ) * (21 * n + 4 : ℤ)) = 1 := by
    ring
  have hgcd_left : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (21 * n + 4 : ℤ) := by
    exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hgcd_right : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (14 * n + 3 : ℤ) := by
    exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hgcd_comb : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (1 : ℤ) := by
    have h1 : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (3 : ℤ) * (14 * n + 3 : ℤ) :=
      dvd_mul_of_dvd_right hgcd_right 3
    have h2 : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ (2 : ℤ) * (21 * n + 4 : ℤ) :=
      dvd_mul_of_dvd_right hgcd_left 2
    have hsub : (Nat.gcd (21 * n + 4) (14 * n + 3) : ℤ) ∣ ((3 : ℤ) * (14 * n + 3 : ℤ) - (2 : ℤ) * (21 * n + 4 : ℤ)) :=
      dvd_sub h1 h2
    rw [hcomb] at hsub
    exact hsub
  have hgcd_nat : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
    exact (Int.ofNat_dvd.mp hgcd_comb)
  exact Nat.dvd_one.mp hgcd_nat
