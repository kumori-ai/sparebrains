import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two natural numbers is $17,402.$ One of the two numbers is divisible by $10.$ If the units digit of that number is erased, the other number is obtained. What is the difference of these two numbers?

$\textbf{(A) }10,272 \qquad \textbf{(B) }11,700 \qquad \textbf{(C) }13,362 \qquad \textbf{(D) }14,238 \qquad \textbf{(E) }15,426$ -/
theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
  have hx_eq : x = 10 * y := by
    calc
      x = (x / 10) * 10 := by symm; exact Nat.div_mul_cancel h₁
      _ = y * 10 := by rw [h₂]
      _ = 10 * y := by rw [mul_comm]
  have hx_eqZ : (x : ℤ) = 10 * (y : ℤ) := by exact_mod_cast hx_eq
  have hsumZ : (x : ℤ) + (y : ℤ) = (17402 : ℤ) := by exact_mod_cast h₀
  linarith
