import Mathlib

open scoped Nat
open scoped Real

/-- Find $24^{-1} \pmod{11^2}$. That is, find the residue $b$ for which $24b \equiv 1\pmod{11^2}$.

Express your answer as an integer from $0$ to $11^2-1$, inclusive. -/
theorem mathd_numbertheory_233 (b : ZMod (11 ^ 2)) (h₀ : b = 24⁻¹) : b = 116 := by
  subst h₀
  have h1 : (24 : ZMod (11 ^ 2))⁻¹ * 24 = 1 := by
    apply ZMod.inv_mul_of_unit
    first
      | exact ⟨⟨24, 116, by decide, by decide⟩, rfl⟩
      | decide
      | exact ⟨24, 116, by decide, by decide⟩
      | exact ⟨116, by decide⟩
  have h2 : (24 : ZMod (11 ^ 2)) * 116 = 1 := by decide
  calc (24 : ZMod (11 ^ 2))⁻¹
      = (24 : ZMod (11 ^ 2))⁻¹ * ((24 : ZMod (11 ^ 2)) * 116) := by rw [h2, mul_one]
    _ = ((24 : ZMod (11 ^ 2))⁻¹ * 24) * 116 := by rw [mul_assoc]
    _ = 116 := by rw [h1, one_mul]
