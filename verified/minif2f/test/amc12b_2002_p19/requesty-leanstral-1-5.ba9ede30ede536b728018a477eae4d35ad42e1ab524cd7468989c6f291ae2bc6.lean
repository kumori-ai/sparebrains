import Mathlib

open scoped Nat
open scoped Real

/--
If $ a$, $ b$, and $ c$ are positive real numbers such that $ a(b +{} c) ={} 152$, $ b(c +{} a) ={} 162$, and $ c(a +{} b) ={} 170$, then abc is

$ \textbf{(A)}\ 672 \qquad
\textbf{(B)}\ 688 \qquad
\textbf{(C)}\ 704 \qquad
\textbf{(D)}\ 720 \qquad
\textbf{(E)}\ 750$ -/
theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have habc_pos : 0 < a * b * c := by positivity
  -- expand the given equations
  have h_ab_ac : a * b + a * c = 152 := by
    calc
      a * b + a * c = a * (b + c) := by ring
      _ = 152 := h₁
  have h_bc_ab : b * c + a * b = 162 := by
    calc
      b * c + a * b = b * (c + a) := by ring
      _ = 162 := h₂
  have h_ac_bc : a * c + b * c = 170 := by
    calc
      a * c + b * c = c * (a + b) := by ring
      _ = 170 := h₃
  -- sum of the three equations gives 2*(ab+bc+ca) = 484
  have h_sum : a * b + b * c + c * a = 242 := by
    linarith
  -- solve for each product
  have h_ab : a * b = 72 := by
    linarith
  have h_bc : b * c = 90 := by
    linarith
  have h_ac : a * c = 80 := by
    linarith
  -- compute (abc)^2
  have h_sq_eq : (a * b * c)^2 = 720^2 := by
    calc
      (a * b * c)^2 = (a * b) * (b * c) * (a * c) := by ring
      _ = 72 * 90 * 80 := by simp [h_ab, h_bc, h_ac]
      _ = 518400 := by norm_num
      _ = 720^2 := by norm_num
  -- deduce abc = 720 using positivity
  have h_factor : (a * b * c - 720) * (a * b * c + 720) = 0 := by
    nlinarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with (h | h)
  · linarith
  · -- h: a*b*c + 720 = 0, impossible because a*b*c > 0
    have : a * b * c > 0 := habc_pos
    linarith
