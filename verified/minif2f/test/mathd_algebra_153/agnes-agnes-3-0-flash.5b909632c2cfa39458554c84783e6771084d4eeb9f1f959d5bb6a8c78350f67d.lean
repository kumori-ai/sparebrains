import Mathlib

open scoped Nat
open scoped Real

/--
We write $\lfloor X \rfloor$ to mean the greatest integer less than or equal to $X$; for example $\lfloor 3\frac{1}{2} \rfloor = 3$. If $N = \frac{1}{3}$, what is the value of $\lfloor 10N \rfloor + \lfloor 100N \rfloor + \lfloor 1000N \rfloor + \lfloor 10,000N \rfloor$? -/
theorem mathd_algebra_153 (n : ℝ) (h₀ : n = 1 / 3) :
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) =
      3702 := by
  subst h₀
  have h₁ : Int.floor (10 : ℝ) / 3 = 3 := by norm_num [Int.floor_eq_iff]
  have h₂ : Int.floor (100 : ℝ) / 3 = 33 := by norm_num [Int.floor_eq_iff]
  have h₃ : Int.floor (1000 : ℝ) / 3 = 333 := by norm_num [Int.floor_eq_iff]
  have h₄ : Int.floor (10000 : ℝ) / 3 = 3333 := by norm_num [Int.floor_eq_iff]
  norm_num [h₁, h₂, h₃, h₄]
