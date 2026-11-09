import Mathlib

open scoped Nat
open scoped Real

/--
In the complex plane, let $A$ be the set of solutions to $z^3 - 8 = 0$ and let $B$ be the set of solutions to $z^3 - 8z^2 - 8z + 64 = 0$. What is the greatest distance between a point of $A$ and a point of $B?$

$\textbf{(A) } 2\sqrt{3} \qquad \textbf{(B) } 6 \qquad \textbf{(C) } 9 \qquad \textbf{(D) } 2\sqrt{21} \qquad \textbf{(E) } 9 + \sqrt{3}$ -/
theorem amc12a_2020_p15 :
    IsGreatest
      { ‖a - b‖ |
        (a : ℂ) (b : ℂ)
        (h₀ : a^3 - 8 = 0)
        (h₁ : b^3 - 8 * b^2 - 8 * b + 64 = 0) } (2 * Real.sqrt 21) := by
  have hs3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2_nonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2_le : Real.sqrt 2 ≤ 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
  have h21 : (2 * Real.sqrt 21 : ℝ) ^ 2 = 84 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hnorm_sq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  constructor
  · -- Membership: take a = -1 + √3 i, b = 8
    refine ⟨-1 + Real.sqrt 3 * Complex.I, 8, ?_, by norm_num, ?_⟩
    · have h2 : (-1 + Real.sqrt 3 * Complex.I) ^ 2
          + 2 * (-1 + Real.sqrt 3 * Complex.I) + 4 = 0 := by
        rw [Complex.ext_iff]
        constructor <;>
          simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hs3] <;>
          ring
      have hfact : (-1 + Real.sqrt 3 * Complex.I) ^ 3 - 8
          = ((-1 + Real.sqrt 3 * Complex.I) - 2)
            * ((-1 + Real.sqrt 3 * Complex.I) ^ 2
              + 2 * (-1 + Real.sqrt 3 * Complex.I) + 4) := by ring
      rw [hfact, h2, mul_zero]
    · have h1 : ‖(-1 + Real.sqrt 3 * Complex.I) - 8‖ ^ 2 = 84 := by
        rw [hnorm_sq]
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        norm_num
      calc ‖(-1 + Real.sqrt 3 * Complex.I) - 8‖
          = Real.sqrt (‖(-1 + Real.sqrt 3 * Complex.I) - 8‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt 84 := by rw [h1]
        _ = 2 * Real.sqrt 21 := by
            rw [← h21]
            exact Real.sqrt_sq (by positivity)
  · -- Upper bound
    intro d hd
    obtain ⟨a, b, ha, hb, rfl⟩ := hd
    have ha3 : a ^ 3 = (8 : ℂ) := sub_eq_zero.mp ha
    have hnorm3 : ‖a‖ ^ 3 = 8 := by
      have h := congrArg (fun z : ℂ => ‖z‖) ha3
      simp [norm_pow] at h
      simpa using h
    have ha_norm : ‖a‖ = 2 := by
      have hfact : (‖a‖ - 2) * (‖a‖ ^ 2 + 2 * ‖a‖ + 4) = 0 := by
        linear_combination hnorm3
      rcases mul_eq_zero.mp hfact with h | h
      · linarith
      · nlinarith [norm_nonneg a, sq_nonneg ‖a‖]
    have ha_sq : a.re ^ 2 + a.im ^ 2 = 4 := by
      have h : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := hnorm_sq a
      rw [ha_norm] at h
      linarith
    have hdist : ‖a - b‖ ^ 2 = (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 := by
      rw [hnorm_sq]
      simp [Complex.sub_re, Complex.sub_im]
    have ha_fact : (a - 2) * (a ^ 2 + 2 * a + 4) = 0 := by
      linear_combination ha
    have hb_fact : (b - 8) * (b ^ 2 - 8) = 0 := by
      linear_combination hb
    have ha_cases : a.re = 2 ∨ a.re = -1 := by
      rcases mul_eq_zero.mp ha_fact with h | h
      · left
        have ha2 : a = 2 := sub_eq_zero.mp h
        rw [ha2]
        simp
      · right
        have hre_raw := congrArg Complex.re h
        have him_raw := congrArg Complex.im h
        simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre_raw him_raw
        have hre : a.re ^ 2 - a.im ^ 2 + 2 * a.re + 4 = 0 := by
          linear_combination hre_raw
        have him : 2 * a.re * a.im + 2 * a.im = 0 := by
          linear_combination him_raw
        have him' : (2 : ℝ) * a.im * (a.re + 1) = 0 := by
          linear_combination him
        rcases mul_eq_zero.mp him' with h1 | h1
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · exfalso
            norm_num at h2
          · exfalso
            nlinarith [hre, sq_nonneg (a.re + 1), sq_nonneg a.im, h2]
        · linarith
    have hb_cases : (b.re = 8 ∧ b.im = 0) ∨ (b.re = 2 * Real.sqrt 2 ∧ b.im = 0)
        ∨ (b.re = -2 * Real.sqrt 2 ∧ b.im = 0) := by
      rcases mul_eq_zero.mp hb_fact with h | h
      · left
        have hb8 : b = 8 := sub_eq_zero.mp h
        constructor <;> rw [hb8] <;> simp
      · have hb2 : b ^ 2 = (8 : ℂ) := sub_eq_zero.mp h
        have hre_raw := congrArg Complex.re hb2
        have him_raw := congrArg Complex.im hb2
        simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre_raw him_raw
        have hre : b.re ^ 2 - b.im ^ 2 = 8 := by
          linear_combination hre_raw
        have him : 2 * b.re * b.im = 0 := by
          linear_combination him_raw
        have hb_im : b.im = 0 := by
          rcases mul_eq_zero.mp him with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exfalso
              norm_num at h2
            · exfalso
              nlinarith [hre, sq_nonneg b.im, h2]
          · exact h1
        have hre2 : b.re ^ 2 = 8 := by
          rw [hb_im] at hre
          linarith
        have hfact : (b.re - 2 * Real.sqrt 2) * (b.re + 2 * Real.sqrt 2) = 0 := by
          linear_combination hre2 - 4 * hs2
        rcases mul_eq_zero.mp hfact with h1 | h1
        · right
          left
          constructor
          · linarith
          · exact hb_im
        · right
          right
          constructor
          · linarith
          · exact hb_im
    rcases ha_cases with ha_re | ha_re <;>
      rcases hb_cases with ⟨hb_re, hb_im⟩ | ⟨hb_re, hb_im⟩ | ⟨hb_re, hb_im⟩
    all_goals
      have hle84 : ‖a - b‖ ^ 2 ≤ 84 := by
        have ha_im : a.im ^ 2 = 4 - a.re ^ 2 := by linarith [ha_sq]
        rw [ha_re] at ha_im
        rw [hdist, hb_im, ha_re, hb_re]
        nlinarith [ha_im, hs2, hs2_nonneg, hs2_le, sq_nonneg a.im,
          sq_nonneg (Real.sqrt 2), mul_nonneg hs2_nonneg hs2_nonneg]
      calc ‖a - b‖ = Real.sqrt (‖a - b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt 84 := Real.sqrt_le_sqrt hle84
        _ = 2 * Real.sqrt 21 := by
            rw [← h21]
            exact Real.sqrt_sq (by positivity)
