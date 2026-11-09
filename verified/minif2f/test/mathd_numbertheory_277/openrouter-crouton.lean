import Mathlib

open scoped Nat
open scoped Real

/--
The greatest common divisor of positive integers $m$ and $n$ is 6. The least common multiple of $m$ and $n$ is 126. What is the least possible value of $m+n$? -/
theorem mathd_numbertheory_277 :
    IsLeast
       {(m + n) | (m : ℕ) (n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126)}
      60 := by
  refine ⟨⟨18, 42, by norm_num, by norm_num, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨m, n, hm, hn, rfl⟩ := hx
  have hm_dvd : 6 ∣ m := hm ▸ Nat.gcd_dvd_left m n
  have hn_dvd : 6 ∣ n := hm ▸ Nat.gcd_dvd_right m n
  obtain ⟨a, rfl⟩ := hm_dvd
  obtain ⟨b, rfl⟩ := hn_dvd
  have hgcd : Nat.gcd a b = 1 := by
    have h := hm
    rw [Nat.gcd_mul_left] at h
    omega
  have hlcm : Nat.lcm a b = 21 := by
    have h := hn
    rw [Nat.lcm_mul_left] at h
    omega
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      simp at hn
    · exact h
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      simp at hn
    · exact h
  have hab : a * b = 21 := by
    have h := Nat.gcd_mul_lcm a b
    rw [hgcd, hlcm] at h
    omega
  have key : 10 ≤ a + b := by
    by_contra hlt
    push_neg at hlt
    have hle9 : a + b ≤ 9 := by omega
    have habZ : (a : ℤ) * (b : ℤ) = 21 := by exact_mod_cast hab
    have hs_nonneg : (0 : ℤ) ≤ (a : ℤ) + (b : ℤ) := by positivity
    have hs_le : (a : ℤ) + (b : ℤ) ≤ 9 := by exact_mod_cast hle9
    have hle : ((a : ℤ) + (b : ℤ)) ^ 2 ≤ 81 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs_le)
        (add_nonneg (by norm_num : (0 : ℤ) ≤ 9) hs_nonneg)]
    have hsq : (0 : ℤ) ≤ ((a : ℤ) - (b : ℤ)) ^ 2 := sq_nonneg _
    nlinarith [hsq, habZ, hle]
  omega
