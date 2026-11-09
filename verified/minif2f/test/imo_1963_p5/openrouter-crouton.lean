import Mathlib

open scoped Nat
open scoped Real

/-- Prove that $\cos{\frac{\pi}{7}}-\cos{\frac{2\pi}{7}}+\cos{\frac{3\pi}{7}}=\frac{1}{2}$ -/
theorem imo_1963_p5 : Real.cos (π / 7) - Real.cos (2 * π / 7) + Real.cos (3 * π / 7) = 1 / 2 := by
  have hsin_pos : 0 < Real.sin (π / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by norm_num))
      (div_lt_self Real.pi_pos (by norm_num))
  have hsin_ne : Real.sin (π / 7) ≠ 0 := ne_of_gt hsin_pos
  have r2 : 2 * π / 7 = 2 * (π / 7) := by ring
  have r3 : 3 * π / 7 = 3 * (π / 7) := by ring
  rw [r2, r3]
  have h1 : 2 * Real.sin (π / 7) * Real.cos (π / 7) = Real.sin (2 * (π / 7)) := by
    rw [Real.sin_two_mul]
  have h2 : 2 * Real.sin (π / 7) * Real.cos (2 * (π / 7))
      = Real.sin (3 * (π / 7)) - Real.sin (π / 7) := by
    have e1 : Real.sin (3 * (π / 7))
        = Real.sin (2 * (π / 7)) * Real.cos (π / 7)
          + Real.cos (2 * (π / 7)) * Real.sin (π / 7) := by
      have h : 3 * (π / 7) = 2 * (π / 7) + π / 7 := by ring
      rw [h, Real.sin_add]
    have e2 : Real.sin (π / 7)
        = Real.sin (2 * (π / 7)) * Real.cos (π / 7)
          - Real.cos (2 * (π / 7)) * Real.sin (π / 7) := by
      calc Real.sin (π / 7) = Real.sin (2 * (π / 7) - π / 7) := by
            congr 1
            ring
        _ = Real.sin (2 * (π / 7)) * Real.cos (π / 7)
            - Real.cos (2 * (π / 7)) * Real.sin (π / 7) :=
            Real.sin_sub _ _
    linear_combination e2 - e1
  have h3 : 2 * Real.sin (π / 7) * Real.cos (3 * (π / 7))
      = Real.sin (4 * (π / 7)) - Real.sin (2 * (π / 7)) := by
    have e1 : Real.sin (4 * (π / 7))
        = Real.sin (3 * (π / 7)) * Real.cos (π / 7)
          + Real.cos (3 * (π / 7)) * Real.sin (π / 7) := by
      have h : 4 * (π / 7) = 3 * (π / 7) + π / 7 := by ring
      rw [h, Real.sin_add]
    have e2 : Real.sin (2 * (π / 7))
        = Real.sin (3 * (π / 7)) * Real.cos (π / 7)
          - Real.cos (3 * (π / 7)) * Real.sin (π / 7) := by
      calc Real.sin (2 * (π / 7)) = Real.sin (3 * (π / 7) - π / 7) := by
            congr 1
            ring
        _ = Real.sin (3 * (π / 7)) * Real.cos (π / 7)
            - Real.cos (3 * (π / 7)) * Real.sin (π / 7) :=
            Real.sin_sub _ _
    linear_combination e2 - e1
  have h4 : Real.sin (4 * (π / 7)) = Real.sin (3 * (π / 7)) := by
    have h : 4 * (π / 7) = π - 3 * (π / 7) := by ring
    rw [h, Real.sin_pi_sub]
  have key : 2 * Real.sin (π / 7)
      * (Real.cos (π / 7) - Real.cos (2 * (π / 7)) + Real.cos (3 * (π / 7)))
      = Real.sin (π / 7) := by
    calc 2 * Real.sin (π / 7)
          * (Real.cos (π / 7) - Real.cos (2 * (π / 7)) + Real.cos (3 * (π / 7)))
        = 2 * Real.sin (π / 7) * Real.cos (π / 7)
          - 2 * Real.sin (π / 7) * Real.cos (2 * (π / 7))
          + 2 * Real.sin (π / 7) * Real.cos (3 * (π / 7)) := by ring
      _ = Real.sin (2 * (π / 7)) - (Real.sin (3 * (π / 7)) - Real.sin (π / 7))
          + (Real.sin (4 * (π / 7)) - Real.sin (2 * (π / 7))) := by rw [h1, h2, h3]
      _ = Real.sin (π / 7) := by rw [h4]; ring
  have hzero : Real.sin (π / 7)
      * (2 * (Real.cos (π / 7) - Real.cos (2 * (π / 7)) + Real.cos (3 * (π / 7))) - 1) = 0 := by
    have h : Real.sin (π / 7)
        * (2 * (Real.cos (π / 7) - Real.cos (2 * (π / 7)) + Real.cos (3 * (π / 7))) - 1)
        = 2 * Real.sin (π / 7)
          * (Real.cos (π / 7) - Real.cos (2 * (π / 7)) + Real.cos (3 * (π / 7)))
          - Real.sin (π / 7) := by ring
    rw [h, key]; ring
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hsin_ne
  · linarith
