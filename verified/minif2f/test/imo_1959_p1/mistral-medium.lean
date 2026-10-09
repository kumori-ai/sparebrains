import Mathlib

open scoped Nat
open scoped Real

/--
Prove that the fraction $ \dfrac{21n +{} 4}{14n +{} 3}$ is irreducible for every natural number $ n$. -/
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
    rw [Nat.gcd_comm]
    rw [show 21 * n + 4 = (14 * n + 3) + (7 * n + 1) by omega]
    norm_num
  have h2 : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) (1) := by
    rw [Nat.gcd_comm]
    rw [show 14 * n + 3 = 2 * (7 * n + 1) + 1 by omega]
    norm_num
  rw [h1, h2]
  simp
