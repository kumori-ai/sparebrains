import Mathlib

open scoped Nat
open scoped Real

/--
We write $\lfloor X \rfloor$ to mean the greatest integer less than or equal to $X$; for example $\lfloor 3\frac{1}{2} \rfloor = 3$. If $N = \frac{1}{3}$, what is the value of $\lfloor 10N \rfloor + \lfloor 100N \rfloor + \lfloor 1000N \rfloor + \lfloor 10,000N \rfloor$? -/
theorem mathd_algebra_153 (n : ℝ) (h₀ : n = 1 / 3) :
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) =
      3702 := by
  rw [h₀]
  have h1 : Int.floor (10 * (1 / 3 : ℝ)) = 3 := by
    rw [Int.floor_eq_iff]
    norm_num
  have h2 : Int.floor (100 * (1 / 3 : ℝ)) = 33 := by
    rw [Int.floor_eq_iff]
    norm_num
  have h3 : Int.floor (1000 * (1 / 3 : ℝ)) = 333 := by
    rw [Int.floor_eq_iff]
    norm_num
  have h4 : Int.floor (10000 * (1 / 3 : ℝ)) = 3333 := by
    rw [Int.floor_eq_iff]
    norm_num
  rw [h1, h2, h3, h4]
  norm_num
