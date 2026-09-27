import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have hxy_pos : 0 < x * y := by
    apply Real.sqrt_pos.1
    rw [h₁]
    norm_num
  have hxy : x * y = 19 := by
    calc
      x * y = (Real.sqrt (x * y)) ^ 2 :=
        (Real.sq_sqrt hxy_pos.le).symm
      _ = (Real.sqrt 19) ^ 2 :=
        congrArg (fun z : ℝ => z ^ 2) h₁
      _ = 19 := Real.sq_sqrt (by norm_num)
  nlinarith [h₀, hxy]
