import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  rcases h₀ with ⟨ha, hb, hc⟩
  set x := b + c - a with hx_def
  set y := c + a - b with hy_def
  set z := a + b - c with hz_def
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hz_pos : 0 < z := by linarith
  have ha_expr : a = (y + z) / 2 := by linarith
  have hb_expr : b = (z + x) / 2 := by linarith
  have hc_expr : c = (x + y) / 2 := by linarith
  rw [ha_expr, hb_expr, hc_expr, hx_def, hy_def, hz_def]
  -- goal: ((y + z) / 2) ^ 2 * x + ((z + x) / 2) ^ 2 * y + ((x + y) / 2) ^ 2 * z ≤ 3 * ((y + z) / 2) * ((z + x) / 2) * ((x + y) / 2)
  field_simp
  ring
  -- Now goal is: 2*(x*(y+z)^2 + y*(z+x)^2 + z*(x+y)^2) ≤ 3*(y+z)*(z+x)*(x+y)
  -- Let's expand both sides and rearrange to the identity.
  -- We can use `nlinarith` here? Or we can use the identity.
  -- Let's compute the difference.
  -- We'll show that 3*(y+z)*(z+x)*(x+y) - 2*(x*(y+z)^2 + y*(z+x)^2 + z*(x+y)^2) = x*(y-z)^2 + y*(z-x)^2 + z*(x-y)^2 ≥ 0.
  -- So we can write:
  have h_nonneg : 0 ≤ x*(y-z)^2 + y*(z-x)^2 + z*(x-y)^2 := by
    positivity
  -- positivity can handle sum of nonnegative terms because x,y,z > 0 and squares ≥ 0.
  -- Then we need to show that the goal is equivalent to that.
  -- We can use `ring` to expand both sides and show equality.
  -- Let's do:
  have h_eq : 3*(y+z)*(z+x)*(x+y) - 2*(x*(y+z)^2 + y*(z+x)^2 + z*(x+y)^2) = x*(y-z)^2 + y*(z-x)^2 + z*(x-y)^2 := by
    ring
  -- Then the goal is `2*(...) ≤ 3*(...)`. This is equivalent to `0 ≤ 3*(...) - 2*(...)`.
  -- So we can `linarith` using `h_eq` and `h_nonneg`.
  linarith
