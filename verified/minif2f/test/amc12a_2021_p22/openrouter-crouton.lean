import Mathlib

open scoped Nat
open scoped Real

/--
Suppose that the roots of the polynomial $P(x)=x^3+ax^2+bx+c$ are $\cos \frac{2\pi}7,\cos \frac{4\pi}7,$ and $\cos \frac{6\pi}7$, where angles are in radians. What is $abc$?

$\textbf{(A) }-\frac{3}{49} \qquad \textbf{(B) }-\frac{1}{28} \qquad \textbf{(C) }\frac{^3\sqrt7}{64} \qquad \textbf{(D) }\frac{1}{32}\qquad \textbf{(E) }\frac{1}{28}$ -/
theorem amc12a_2021_p22 (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 3 + a * x ^ 2 + b * x + c)
    (h₁ :
      f ⁻¹' {0} =
        {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)}) :
    a * b * c = 1 / 32 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Vieta's formulas for a monic cubic with three distinct roots.
  have key : ∀ (A B C x y z : ℝ), x ≠ y → y ≠ z → x ≠ z →
      x ^ 3 + A * x ^ 2 + B * x + C = 0 →
      y ^ 3 + A * y ^ 2 + B * y + C = 0 →
      z ^ 3 + A * z ^ 2 + B * z + C = 0 →
      A = -(x + y + z) ∧ B = x * y + x * z + y * z ∧ C = -(x * y * z) := by
    intro A B C x y z hxy hyz hxz ex ey ez
    have dxy : (x ^ 2 + x * y + y ^ 2) + A * (x + y) + B = 0 := by
      have h : (x - y) * ((x ^ 2 + x * y + y ^ 2) + A * (x + y) + B) = 0 := by
        have heq : (x - y) * ((x ^ 2 + x * y + y ^ 2) + A * (x + y) + B) =
            (x ^ 3 + A * x ^ 2 + B * x + C) - (y ^ 3 + A * y ^ 2 + B * y + C) := by ring
        rw [heq, ex, ey]; norm_num
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hxy
      · exact h1
    have dyz : (y ^ 2 + y * z + z ^ 2) + A * (y + z) + B = 0 := by
      have h : (y - z) * ((y ^ 2 + y * z + z ^ 2) + A * (y + z) + B) = 0 := by
        have heq : (y - z) * ((y ^ 2 + y * z + z ^ 2) + A * (y + z) + B) =
            (y ^ 3 + A * y ^ 2 + B * y + C) - (z ^ 3 + A * z ^ 2 + B * z + C) := by ring
        rw [heq, ey, ez]; norm_num
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hyz
      · exact h1
    have hA : A = -(x + y + z) := by
      have h : (x - z) * (A + (x + y + z)) = 0 := by
        have heq : (x - z) * (A + (x + y + z)) =
            ((x ^ 2 + x * y + y ^ 2) + A * (x + y) + B) -
            ((y ^ 2 + y * z + z ^ 2) + A * (y + z) + B) := by ring
        rw [heq, dxy, dyz]; norm_num
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hxz
      · linarith
    have hB : B = x * y + x * z + y * z := by
      have hd := dxy
      rw [hA] at hd
      linear_combination hd
    have hC : C = -(x * y * z) := by
      have he := ex
      rw [hA, hB] at he
      linear_combination he
    exact ⟨hA, hB, hC⟩
  -- The three cosines are distinct.
  have hne12 : Real.cos (2 * Real.pi / 7) ≠ Real.cos (4 * Real.pi / 7) := by
    have hlt : Real.cos (4 * Real.pi / 7) < Real.cos (2 * Real.pi / 7) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    exact ne_of_gt hlt
  have hne23 : Real.cos (4 * Real.pi / 7) ≠ Real.cos (6 * Real.pi / 7) := by
    have hlt : Real.cos (6 * Real.pi / 7) < Real.cos (4 * Real.pi / 7) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    exact ne_of_gt hlt
  have hne13 : Real.cos (2 * Real.pi / 7) ≠ Real.cos (6 * Real.pi / 7) := by
    have hlt : Real.cos (6 * Real.pi / 7) < Real.cos (2 * Real.pi / 7) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    exact ne_of_gt hlt
  -- Each cosine is a root of `f`.
  have hf1 : f (Real.cos (2 * Real.pi / 7)) = 0 := by
    have hm : Real.cos (2 * Real.pi / 7) ∈ f ⁻¹' {0} := by
      rw [h₁]; simp
    simpa using hm
  have hf2 : f (Real.cos (4 * Real.pi / 7)) = 0 := by
    have hm : Real.cos (4 * Real.pi / 7) ∈ f ⁻¹' {0} := by
      rw [h₁]; simp
    simpa using hm
  have hf3 : f (Real.cos (6 * Real.pi / 7)) = 0 := by
    have hm : Real.cos (6 * Real.pi / 7) ∈ f ⁻¹' {0} := by
      rw [h₁]; simp
    simpa using hm
  have e1 : (Real.cos (2 * Real.pi / 7)) ^ 3 + a * (Real.cos (2 * Real.pi / 7)) ^ 2 +
      b * (Real.cos (2 * Real.pi / 7)) + c = 0 := by
    have h := hf1; rw [h₀] at h; exact h
  have e2 : (Real.cos (4 * Real.pi / 7)) ^ 3 + a * (Real.cos (4 * Real.pi / 7)) ^ 2 +
      b * (Real.cos (4 * Real.pi / 7)) + c = 0 := by
    have h := hf2; rw [h₀] at h; exact h
  have e3 : (Real.cos (6 * Real.pi / 7)) ^ 3 + a * (Real.cos (6 * Real.pi / 7)) ^ 2 +
      b * (Real.cos (6 * Real.pi / 7)) + c = 0 := by
    have h := hf3; rw [h₀] at h; exact h
  -- Trigonometric helpers.
  have cos_four_pi_sub : ∀ x : ℝ, Real.cos (4 * Real.pi - x) = Real.cos x := by
    intro x
    rw [show 4 * Real.pi - x = 2 * Real.pi - (x - 2 * Real.pi) by ring,
      Real.cos_two_pi_sub, Real.cos_sub_two_pi]
  have cos_six_pi_sub : ∀ x : ℝ, Real.cos (6 * Real.pi - x) = Real.cos x := by
    intro x
    rw [show 6 * Real.pi - x = 4 * Real.pi - (x - 2 * Real.pi) by ring,
      cos_four_pi_sub, Real.cos_sub_two_pi]
  have ne_one : ∀ t : ℝ, 0 < t → t < Real.pi → Real.cos t ≠ 1 := by
    intro t h0 hpi' h
    have hs := Real.sin_pos_of_pos_of_lt_pi h0 hpi'
    have hsq : (Real.sin t) ^ 2 = 0 := by
      have h1 := Real.sin_sq_add_cos_sq t
      rw [h] at h1
      linarith
    have hz : Real.sin t = 0 := by simpa using hsq
    linarith
  have cubic_of : ∀ t : ℝ, Real.cos (4 * t) = Real.cos (3 * t) → Real.cos t ≠ 1 →
      8 * (Real.cos t) ^ 3 + 4 * (Real.cos t) ^ 2 - 4 * (Real.cos t) - 1 = 0 := by
    intro t hcos hne
    have h3 := Real.cos_three_mul t
    have h2 := Real.cos_two_mul t
    have h4 : Real.cos (4 * t) = 8 * (Real.cos t) ^ 4 - 8 * (Real.cos t) ^ 2 + 1 := by
      have h : Real.cos (4 * t) = 2 * (Real.cos (2 * t)) ^ 2 - 1 := by
        rw [show 4 * t = 2 * (2 * t) by ring]
        exact Real.cos_two_mul (2 * t)
      rw [h, h2]; ring
    have hfact : (Real.cos t - 1) *
        (8 * (Real.cos t) ^ 3 + 4 * (Real.cos t) ^ 2 - 4 * (Real.cos t) - 1) = 0 := by
      linear_combination hcos - h4 + h3
    rcases mul_eq_zero.mp hfact with h1 | h1
    · exfalso; apply hne; linarith
    · exact h1
  -- Each cosine satisfies `8r^3 + 4r^2 - 4r - 1 = 0`.
  have hc1 : Real.cos (4 * (2 * Real.pi / 7)) = Real.cos (3 * (2 * Real.pi / 7)) := by
    rw [show 4 * (2 * Real.pi / 7) = 2 * Real.pi - 3 * (2 * Real.pi / 7) by ring]
    exact Real.cos_two_pi_sub _
  have hc2 : Real.cos (4 * (4 * Real.pi / 7)) = Real.cos (3 * (4 * Real.pi / 7)) := by
    rw [show 4 * (4 * Real.pi / 7) = 4 * Real.pi - 3 * (4 * Real.pi / 7) by ring]
    exact cos_four_pi_sub _
  have hc3 : Real.cos (4 * (6 * Real.pi / 7)) = Real.cos (3 * (6 * Real.pi / 7)) := by
    rw [show 4 * (6 * Real.pi / 7) = 6 * Real.pi - 3 * (6 * Real.pi / 7) by ring]
    exact cos_six_pi_sub _
  have E1 := cubic_of _ hc1 (ne_one _ (by linarith) (by linarith))
  have E2 := cubic_of _ hc2 (ne_one _ (by linarith) (by linarith))
  have E3 := cubic_of _ hc3 (ne_one _ (by linarith) (by linarith))
  have g1 : (Real.cos (2 * Real.pi / 7)) ^ 3 + (1 / 2) * (Real.cos (2 * Real.pi / 7)) ^ 2 +
      (-1 / 2) * (Real.cos (2 * Real.pi / 7)) + (-1 / 8) = 0 := by linarith [E1]
  have g2 : (Real.cos (4 * Real.pi / 7)) ^ 3 + (1 / 2) * (Real.cos (4 * Real.pi / 7)) ^ 2 +
      (-1 / 2) * (Real.cos (4 * Real.pi / 7)) + (-1 / 8) = 0 := by linarith [E2]
  have g3 : (Real.cos (6 * Real.pi / 7)) ^ 3 + (1 / 2) * (Real.cos (6 * Real.pi / 7)) ^ 2 +
      (-1 / 2) * (Real.cos (6 * Real.pi / 7)) + (-1 / 8) = 0 := by linarith [E3]
  -- Apply Vieta's formulas to both cubics.
  obtain ⟨ha, hb, hc⟩ := key a b c _ _ _ hne12 hne23 hne13 e1 e2 e3
  obtain ⟨hA2, hB2, hC2⟩ := key (1 / 2) (-1 / 2) (-1 / 8) _ _ _ hne12 hne23 hne13 g1 g2 g3
  have ha' : a = 1 / 2 := by linarith
  have hb' : b = -1 / 2 := by linarith
  have hc' : c = -1 / 8 := by linarith
  rw [ha', hb', hc']; norm_num
