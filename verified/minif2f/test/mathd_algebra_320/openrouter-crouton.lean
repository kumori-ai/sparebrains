import Mathlib

open scoped Nat
open scoped Real

/--
Let $x$ be a positive number such that $2x^2 = 4x + 9.$ If $x$ can be written in simplified form as $\dfrac{a + \sqrt{b}}{c}$ such that $a,$ $b,$ and $c$ are positive integers, what is $a + b + c$? -/
theorem mathd_algebra_320 (x : NNReal) (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 2 * x ^ 2 = 4 * x + 9) (h₂ : x = (a + NNReal.sqrt b) / c)
    (h₃ : (¬∃ n > 1, n ∣ a ∧ n ^ 2 ∣ b ∧ n ∣ c) ∧ ¬IsSquare b) : a + b + c = 26 := by
  obtain ⟨ha, hb, hc⟩ := h₀
  obtain ⟨hcop, hnsq⟩ := h₃
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hxR : (x : ℝ) = ((a : ℝ) + Real.sqrt (b : ℝ)) / (c : ℝ) := by
    have h := congrArg (fun y : NNReal => (y : ℝ)) h₂
    simpa using h
  have h1R : 2 * (x : ℝ) ^ 2 = 4 * (x : ℝ) + 9 := by
    have h := congrArg (fun y : NNReal => (y : ℝ)) h₁
    simpa using h
  have hS2 : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have h_eq : 2 * ((a : ℝ) + Real.sqrt (b : ℝ)) ^ 2
      = 4 * ((a : ℝ) + Real.sqrt (b : ℝ)) * (c : ℝ) + 9 * (c : ℝ) ^ 2 := by
    have h := h1R
    rw [hxR] at h
    calc 2 * ((a : ℝ) + Real.sqrt (b : ℝ)) ^ 2
        = 2 * (((a : ℝ) + Real.sqrt (b : ℝ)) / (c : ℝ)) ^ 2 * (c : ℝ) ^ 2 := by
          field_simp
      _ = (4 * (((a : ℝ) + Real.sqrt (b : ℝ)) / (c : ℝ)) + 9) * (c : ℝ) ^ 2 := by
          rw [h]
      _ = 4 * ((a : ℝ) + Real.sqrt (b : ℝ)) * (c : ℝ) + 9 * (c : ℝ) ^ 2 := by
          field_simp
  have hPQ : (2 * (a : ℝ) ^ 2 + 2 * (b : ℝ) - 4 * (a : ℝ) * (c : ℝ) - 9 * (c : ℝ) ^ 2)
      + (4 * (a : ℝ) - 4 * (c : ℝ)) * Real.sqrt (b : ℝ) = 0 := by
    linear_combination h_eq - 2 * hS2
  have hirr : Irrational (Real.sqrt (b : ℝ)) := irrational_sqrt_natCast_iff.mpr hnsq
  have hQ0 : ∀ p q : ℤ, (p : ℝ) + (q : ℝ) * Real.sqrt (b : ℝ) = 0 → q = 0 := by
    intro p q h
    by_contra hq
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have hr : ((-p / q : ℚ) : ℝ) = Real.sqrt (b : ℝ) := by
      have hcast : ((-p / q : ℚ) : ℝ) = -(p : ℝ) / (q : ℝ) := by
        push_cast
        ring
      rw [hcast, div_eq_iff hqR]
      linear_combination -h
    exact hirr ⟨-p / q, hr⟩
  have hQi0 : (4 * (a : ℤ) - 4 * (c : ℤ)) = 0 :=
    hQ0 (2 * (a : ℤ) ^ 2 + 2 * (b : ℤ) - 4 * (a : ℤ) * (c : ℤ) - 9 * (c : ℤ) ^ 2)
      (4 * (a : ℤ) - 4 * (c : ℤ)) (by push_cast; linear_combination hPQ)
  have hac : a = c := by
    have h1 : (a : ℤ) = (c : ℤ) := by linarith [hQi0]
    exact_mod_cast h1
  rw [← hac] at hPQ
  have hb_eq : 2 * b = 11 * a ^ 2 := by
    have hR : (2 * b : ℝ) = (11 * a ^ 2 : ℝ) := by
      linear_combination hPQ
    exact_mod_cast hR
  have hdiv : 2 ∣ a ^ 2 := by
    have h1 : 2 ∣ 11 * a ^ 2 := ⟨b, hb_eq.symm⟩
    rcases (Nat.prime_two.dvd_mul).mp h1 with h | h
    · norm_num at h
    · exact h
  have ha2 : 2 ∣ a := Nat.prime_two.dvd_of_dvd_pow hdiv
  obtain ⟨k, hk⟩ := ha2
  have hkpos : 0 < k := by omega
  have hb_eq2 : b = 22 * k ^ 2 := by
    have h := hb_eq
    rw [hk] at h
    have hexp : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    rw [hexp] at h
    omega
  have hk1 : k = 1 := by
    by_contra hkne
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hkne
    apply hcop
    refine ⟨p, hpprime.one_lt, ?_, ?_⟩
    · rw [hk]
      exact dvd_mul_of_dvd_right hpdvd 2
    · exact ⟨by rw [hb_eq2]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpdvd 2) 22,
        by rw [← hac, hk]; exact dvd_mul_of_dvd_right hpdvd 2⟩
  have ha_val : a = 2 := by rw [hk, hk1]
  have hb_val : b = 22 := by rw [hb_eq2, hk1]; norm_num
  omega
