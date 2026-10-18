import Mathlib

open scoped Nat
open scoped Real

/--
If $ x$, $ y$, and $ z$ are positive numbers satisfying \[x +{} 1/y ={} 4,\quad  y +{} 1/z ={} 1,\quad\text{and}\quad z +{} 1/x ={} 7/3,\] then $ xyz ={}$

$ \textbf{(A)}\ 2/3 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 4/3 \qquad \textbf{(D)}\ 2 \qquad \textbf{(E)}\ 7/3$ -/
theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  rcases h₀ with ⟨hx, hy, hz⟩
  -- product of the three equations
  have hprod : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = (28 / 3 : ℝ) := by
    calc
      (x + 1 / y) * (y + 1 / z) * (z + 1 / x)
          = (4 : ℝ) * 1 * (7 / 3) := by
            aesop
      _ = (28 / 3 : ℝ) := by norm_num
  -- expand the product
  have h_expand :
      (x + 1 / y) * (y + 1 / z) * (z + 1 / x) =
        x * y * z + x + y + z + 1 / x + 1 / y + 1 / z + 1 / (x * y * z) := by
    field_simp [mul_comm, mul_left_comm, mul_assoc] ; ring
  have h_eq :
      x * y * z + x + y + z + 1 / x + 1 / y + 1 / z + 1 / (x * y * z) = (28 / 3 : ℝ) := by
    linarith
  -- rewrite reciprocals using the given equations
  have hx_inv : 1 / x = (7 / 3 : ℝ) - z := by
    linarith [h₃]
  have hy_inv : 1 / y = (4 : ℝ) - x := by
    linarith [h₁]
  have hz_inv : 1 / z = (1 : ℝ) - y := by
    linarith [h₂]
  have h_eq2 :
      x * y * z + x + y + z + ((7 / 3 : ℝ) - z) + ((4 : ℝ) - x) + ((1 : ℝ) - y) +
        1 / (x * y * z) = (28 / 3 : ℝ) := by
    simpa [hx_inv, hy_inv, hz_inv] using h_eq
  have h_rel : x * y * z + 1 / (x * y * z) = (2 : ℝ) := by
    linarith
  have hpos : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  have hne : x * y * z ≠ 0 := ne_of_gt hpos
  have h_mul : (x * y * z) ^ 2 + 1 = 2 * (x * y * z) := by
    have := congrArg (fun t : ℝ => (x * y * z) * t) h_rel
    have h' := this
    field_simp [hne] at h'
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h'
  have h_quad : (x * y * z) ^ 2 - 2 * (x * y * z) + 1 = 0 := by
    linarith
  have h_sq : (x * y * z - 1) ^ 2 = 0 := by
    have : (x * y * z - 1) ^ 2 = (x * y * z) ^ 2 - 2 * (x * y * z) + 1 := by ring
    simpa [this] using h_quad
  have h_one : x * y * z - 1 = (0 : ℝ) := (sq_eq_zero_iff.mp h_sq)
  linarith