import Mathlib

open scoped Nat
open scoped Real

/--
Given that $(1+\sin t)(1+\cos t)=5/4$ and \[ (1-\sin t)(1-\cos t)=\frac mn-\sqrt{k}, \] where $k, m,$ and $n$ are positive integers with $m$ and $n$ relatively prime, find $k+m+n.$ -/
theorem aime_1995_p7 (k m n : ℕ) (t : ℝ) (h₀ : 0 < k ∧ 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 1)
    (h₂ : (1 + Real.sin t) * (1 + Real.cos t) = 5 / 4)
    (h₃ : (1 - Real.sin t) * (1 - Real.cos t) = m / n - Real.sqrt k) : k + m + n = 27 := by
  obtain ⟨hk, hm, hn⟩ := h₀
  have hsc : (Real.sin t) ^ 2 + (Real.cos t) ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  have h1 : (Real.sin t + Real.cos t) ^ 2 = 1 + 2 * (Real.sin t * Real.cos t) := by
    have h : (Real.sin t + Real.cos t) ^ 2 = (Real.sin t) ^ 2 + (Real.cos t) ^ 2 + 2 * (Real.sin t * Real.cos t) := by ring
    rw [h, hsc]
  have h2exp : 1 + (Real.sin t + Real.cos t) + Real.sin t * Real.cos t = 5 / 4 := by
    have h : (1 + Real.sin t) * (1 + Real.cos t) = 1 + (Real.sin t + Real.cos t) + Real.sin t * Real.cos t := by ring
    linarith [h₂]
  have hAeq : 2 * (Real.sin t + Real.cos t) ^ 2 + 4 * (Real.sin t + Real.cos t) - 3 = 0 := by
    linear_combination 2 * h1 + 4 * h2exp
  have hA1 : (Real.sin t + Real.cos t + 1) ^ 2 = 5 / 2 := by
    linear_combination hAeq / 2
  have hu2 : (Real.sqrt 10 / 2) ^ 2 = 5 / 2 := by
    have h : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
    linear_combination h / 4
  have hu_pos : 0 < Real.sqrt 10 / 2 := by
    apply div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hu_gt1 : 1 < Real.sqrt 10 / 2 := by
    by_contra h
    push_neg at h
    have h1 : Real.sqrt 10 ≤ 2 := by linarith
    have h2 : (Real.sqrt 10) ^ 2 ≤ 4 := by nlinarith [Real.sqrt_nonneg 10, h1]
    rw [Real.sq_sqrt (by norm_num)] at h2
    norm_num at h2
  have hA_or : Real.sin t + Real.cos t + 1 = Real.sqrt 10 / 2 ∨ Real.sin t + Real.cos t + 1 = -(Real.sqrt 10 / 2) := by
    have hsq : (Real.sin t + Real.cos t + 1) ^ 2 = (Real.sqrt 10 / 2) ^ 2 := by rw [hA1, hu2]
    grind
  have hA_bound : (Real.sin t + Real.cos t) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (Real.sin t - Real.cos t), hsc]
  have hA_val : Real.sin t + Real.cos t = -1 + Real.sqrt 10 / 2 := by
    rcases hA_or with h | h
    · linarith
    · exfalso
      have hAeq2 : Real.sin t + Real.cos t = -1 - Real.sqrt 10 / 2 := by linarith
      have hgt : 4 < (Real.sin t + Real.cos t) ^ 2 := by
        rw [hAeq2]
        nlinarith [hu_gt1, hu_pos]
      linarith [hA_bound, hgt]
  have hE : (1 - Real.sin t) * (1 - Real.cos t) = 13 / 4 - Real.sqrt 10 := by
    have hexp : (1 - Real.sin t) * (1 - Real.cos t) = 1 - (Real.sin t + Real.cos t) + Real.sin t * Real.cos t := by ring
    have hprod : Real.sin t * Real.cos t = 1 / 4 - (Real.sin t + Real.cos t) := by
      linear_combination h2exp
    rw [hexp, hprod, hA_val]
    ring
  have hEq : (m : ℝ) / n - Real.sqrt k = 13 / 4 - Real.sqrt 10 := by
    have h := h₃
    rw [hE] at h
    exact h.symm
  set r : ℚ := (m : ℚ) / (n : ℚ) - 13 / 4 with hr_def
  have hr_cast : (r : ℝ) = (m : ℝ) / (n : ℝ) - 13 / 4 := by
    aesop
  have hsqrt_eq : Real.sqrt k = Real.sqrt 10 + (r : ℝ) := by
    rw [hr_cast]
    linarith [hEq]
  have hirr : Irrational (Real.sqrt 10) := by
    have hirr' : Irrational (Real.sqrt ((10 : ℕ) : ℝ)) := by
      rw [irrational_sqrt_natCast_iff]
      intro hsq
      obtain ⟨a, ha⟩ := hsq
      have ha_le : a ≤ 3 := by
        by_contra hlt
        push_neg at hlt
        have h4 : 4 ≤ a := hlt
        have h16 : 16 ≤ a * a := by
          calc 16 = 4 * 4 := by norm_num
          _ ≤ a * a := Nat.mul_le_mul h4 h4
        omega
      interval_cases a <;> norm_num at ha
    simpa using hirr'
  have hr_zero : r = 0 := by
    by_contra hr_ne
    have hk_eq : (k : ℝ) = 10 + (r : ℝ) ^ 2 + 2 * (r : ℝ) * Real.sqrt 10 := by
      have h1 : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
      have h2 : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
      have h3 : (k : ℝ) = (Real.sqrt 10 + (r : ℝ)) ^ 2 := by
        rw [← h1, hsqrt_eq]
      rw [h3]
      linear_combination h2
    have hr_ne_real : (r : ℝ) ≠ 0 := by exact_mod_cast hr_ne
    have hsqrt_rat : Real.sqrt 10 = ((k : ℝ) - 10 - (r : ℝ) ^ 2) / (2 * (r : ℝ)) := by
      rw [eq_div_iff (mul_ne_zero (by norm_num) hr_ne_real)]
      linear_combination -hk_eq
    set q : ℚ := ((k : ℚ) - 10 - r ^ 2) / (2 * r) with hq_def
    have hq_eq : Real.sqrt 10 = (q : ℝ) := by
      rw [hq_def]
      push_cast
      exact hsqrt_rat
    exact hirr ⟨q, hq_eq.symm⟩
  have hmn : (m : ℚ) / (n : ℚ) = 13 / 4 := by
    have h : (m : ℚ) / (n : ℚ) - 13 / 4 = 0 := by
      rw [← hr_def]
      exact hr_zero
    exact sub_eq_zero.mp h
  have hmn_nat : 4 * m = 13 * n := by
    have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have h2 : (m : ℚ) * 4 = 13 * (n : ℚ) := by
      rw [div_eq_div_iff hn_ne (by norm_num)] at hmn
      exact hmn
    have h3 : ((4 * m : ℕ) : ℚ) = ((13 * n : ℕ) : ℚ) := by push_cast; linarith [h2]
    exact_mod_cast h3
  have hk10 : k = 10 := by
    have hsqrt : Real.sqrt k = Real.sqrt 10 := by
      rw [hsqrt_eq, hr_zero]
      simp
    have h : (Real.sqrt (k : ℝ)) ^ 2 = (Real.sqrt 10) ^ 2 := by rw [hsqrt]
    rw [Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt (by norm_num)] at h
    exact_mod_cast h
  have h13_dvd_m : 13 ∣ m := by
    have hprime : Nat.Prime 13 := by norm_num
    have hdvd : 13 ∣ 4 * m := ⟨n, hmn_nat⟩
    rcases (Nat.Prime.dvd_mul hprime).mp hdvd with h | h
    · norm_num at h
    · exact h
  have h4_dvd_n : 4 ∣ n := by
    have hdvd : 4 ∣ 13 * n := ⟨m, hmn_nat.symm⟩
    have hcop : Nat.Coprime 4 13 := by decide
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨a, ha⟩ := h13_dvd_m
  obtain ⟨b, hb⟩ := h4_dvd_n
  have hab : a = b := by
    have h := hmn_nat
    rw [ha, hb] at h
    omega
  have ha1 : a = 1 := by
    have hgcd : Nat.gcd m n = 1 := h₁
    rw [ha, hb, hab] at hgcd
    have h : Nat.gcd (13 * a) (4 * a) = a := by
      have h1 : Nat.gcd (13 * a) (4 * a) = a * Nat.gcd 13 4 := by
        rw [mul_comm 13 a, mul_comm 4 a, Nat.gcd_mul_left]
      rw [h1]
      norm_num
    aesop
  have hm13 : m = 13 := by rw [ha, ha1]
  have hn4 : n = 4 := by
    omega
  rw [hk10, hm13, hn4]
