import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the final three digits of the integer representation of $5^{100}$? -/
theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by
  have hd : Nat.digits 10 (5 ^ 100 % 1000) = [5, 2, 6] := by
    norm_num [Nat.digits, Nat.digitsAux]
  have hEq : [c, b, a] = [5, 2, 6] := h₁.symm.trans hd
  simp only [List.cons.injEq] at hEq
  omega
