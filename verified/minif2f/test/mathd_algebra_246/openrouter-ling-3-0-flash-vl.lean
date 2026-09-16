import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h_f3 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by simp [h₀]
  have h_fneg3 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := by simp [h₀]
  have h_even : a * 3 ^ 4 - b * 3 ^ 2 = a * (-3) ^ 4 - b * (-3) ^ 2 := by ring
  have h_sum : (3 + 5) + ((-3) + 5) = 10 := by norm_num
  -- f(3) = (a*3^4 - b*3^2) + 8
  -- f(-3) = (a*(-3)^4 - b*(-3)^2) + 2
  -- Since a*3^4 - b*3^2 = a*(-3)^4 - b*(-3)^2, call this E
  -- f(3) = E + 8, f(-3) = E + 2
  -- So f(3) = f(-3) + 6 = 2 + 6 = 8
  
  have h_eq : f 3 = f (-3) + ((3 + 5) - ((-3) + 5)) := by
    calc f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by simp [h₀]
    _ = (a * (-3) ^ 4 - b * (-3) ^ 2) + 3 + 5 := by rw [h_even]
    _ = (a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5) + ((3 + 5) - ((-3) + 5)) := by ring
    _ = f (-3) + ((3 + 5) - ((-3) + 5)) := by rw [h_fneg3]
  rw [h₂] at h_eq
  norm_num at h_eq
  exact h_eq
