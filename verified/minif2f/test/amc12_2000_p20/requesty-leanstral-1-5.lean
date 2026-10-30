import Mathlib

open scoped Nat
open scoped Real

/--
If $ x$, $ y$, and $ z$ are positive numbers satisfying \[x +{} 1/y ={} 4,\quad  y +{} 1/z ={} 1,\quad\text{and}\quad z +{} 1/x ={} 7/3,\] then $ xyz ={}$

$ \textbf{(A)}\ 2/3 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 4/3 \qquad \textbf{(D)}\ 2 \qquad \textbf{(E)}\ 7/3$ -/
theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  rcases h₀ with ⟨hxpos, hypos, hzpos⟩
  have hxne : x ≠ 0 := by linarith
  have hyne : y ≠ 0 := by linarith
  have hzne : z ≠ 0 := by linarith
  field_simp [hyne] at h₁
  field_simp [hzne] at h₂
  field_simp [hxne] at h₃
  -- h₁: x*y + 1 = 4*y
  -- h₂: y*z + 1 = z
  -- h₃: z*x + 1 = (7/3)*x
  have hxyeq : x * y = 4 * y - 1 := by linarith
  have hyzeq : y * z = z - 1 := by linarith
  have hzxeq : z * x = (7/3 : ℝ) * x - 1 := by linarith
  have hP1 : x * y * z = 3 * z - 4 := by
    calc
      x * y * z = (x * y) * z := by ring
      _ = (4 * y - 1) * z := by rw [hxyeq]
      _ = 4 * y * z - z := by ring
      _ = 4 * (y * z) - z := by ring
      _ = 4 * (z - 1) - z := by rw [hyzeq]
      _ = 3 * z - 4 := by ring
  have hP2 : x * y * z = (4/3 : ℝ) * x - 1 := by
    calc
      x * y * z = (y * z) * x := by ring
      _ = (z - 1) * x := by rw [hyzeq]
      _ = z * x - x := by ring
      _ = ((7/3 : ℝ) * x - 1) - x := by rw [hzxeq]
      _ = (4/3 : ℝ) * x - 1 := by ring
  have hP3 : x * y * z = (25/3 : ℝ) * y - 7/3 := by
    calc
      x * y * z = (z * x) * y := by ring
      _ = ((7/3 : ℝ) * x - 1) * y := by rw [hzxeq]
      _ = (7/3 : ℝ) * x * y - y := by ring
      _ = (7/3 : ℝ) * (x * y) - y := by ring
      _ = (7/3 : ℝ) * (4 * y - 1) - y := by rw [hxyeq]
      _ = (25/3 : ℝ) * y - 7/3 := by ring
  have h_eq12 : 3 * z - 4 = (4/3 : ℝ) * x - 1 := by
    rw [← hP1, ← hP2]
  have h_eq13 : 3 * z - 4 = (25/3 : ℝ) * y - 7/3 := by
    rw [← hP1, ← hP3]
  have hyz_eq : 25 * y = 9 * z - 5 := by
    linarith
  have hz_eq : (3 * z - 5)^2 = 0 := by
    calc
      (3 * z - 5)^2 = 9 * z ^ 2 - 30 * z + 25 := by ring
      _ = (9 * z - 5) * z - 25 * (z - 1) := by ring
      _ = (25 * y) * z - 25 * (z - 1) := by rw [hyz_eq]
      _ = 25 * (y * z) - 25 * (z - 1) := by ring
      _ = 25 * (z - 1) - 25 * (z - 1) := by rw [hyzeq]
      _ = 0 := by ring
  have hz_eq' : 3 * z - 5 = 0 := by
    nlinarith
  have hzval : z = 5/3 := by linarith
  have hyval : y = 2/5 := by
    rw [hzval] at hyzeq
    linarith
  have hxval : x = 3/2 := by
    rw [hyval] at hxyeq
    linarith
  calc
    x * y * z = (3/2) * (2/5) * (5/3) := by rw [hxval, hyval, hzval]
    _ = 1 := by norm_num
