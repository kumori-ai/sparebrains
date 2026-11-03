import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of the following expression?
$$\frac{100^2-7^2}{70^2-11^2} \cdot \frac{(70-11)(70+11)}{(100-7)(100+7)}$$
$\textbf{(A) } 1 \qquad \textbf{(B) } \frac{9951}{9950} \qquad \textbf{(C) } \frac{4780}{4779} \qquad \textbf{(D) } \frac{108}{107} \qquad \textbf{(E) } \frac{81}{80} $ -/
theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 := by
  have h1 : (100 : ℝ) ^ 2 - 7 ^ 2 = (100 - 7) * (100 + 7) := by ring
  have h2 : (70 : ℝ) ^ 2 - 11 ^ 2 = (70 - 11) * (70 + 11) := by ring
  rw [h1, h2]
  have h3 : (70 - 11 : ℝ) ≠ 0 := by norm_num
  have h4 : (70 + 11 : ℝ) ≠ 0 := by norm_num
  have h5 : (100 - 7 : ℝ) ≠ 0 := by norm_num
  have h6 : (100 + 7 : ℝ) ≠ 0 := by norm_num
  field_simp [h3, h4, h5, h6]
