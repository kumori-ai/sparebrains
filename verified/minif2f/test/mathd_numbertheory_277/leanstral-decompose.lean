import Mathlib

open scoped Nat
open scoped Real

/--
The greatest common divisor of positive integers $m$ and $n$ is 6. The least common multiple of $m$ and $n$ is 126. What is the least possible value of $m+n$? -/
theorem mathd_numbertheory_277 :
    IsLeast
       {(m + n) | (m : ℕ) (n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126)}
      60 := by
  constructor
  · use 18, 42
    norm_num
  · intro x hx
    rcases hx with ⟨m, n, h₀, h₁, hx_eq⟩
    rw [← hx_eq]
    have h6m : 6 ∣ m := by
      rw [← h₀]
      exact Nat.gcd_dvd_left m n
    have h6n : 6 ∣ n := by
      rw [← h₀]
      exact Nat.gcd_dvd_right m n
    rcases h6m with ⟨a, hm⟩
    rcases h6n with ⟨b, hn⟩
    have hprod : m * n = 756 := by
      calc
        m * n = Nat.gcd m n * Nat.lcm m n := by symm; exact Nat.gcd_mul_lcm m n
        _ = 6 * 126 := by rw [h₀, h₁]
        _ = 756 := by norm_num
    rw [hm, hn] at hprod
    have hab : a * b = 21 := by
      zify at hprod
      have h_ab : (a : ℤ) * (b : ℤ) = 21 := by
        nlinarith
      exact_mod_cast h_ab
    have ha_dvd : a ∣ 21 := by
      rw [← hab]
      exact ⟨b, rfl⟩
    have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos ha_dvd (by norm_num)
    have ha_le : a ≤ 21 := Nat.le_of_dvd (by norm_num) ha_dvd
    have h_cases : a = 1 ∨ a = 3 ∨ a = 7 ∨ a = 21 := by
      have h_divs : Nat.divisors 21 = {1, 3, 7, 21} := by
        decide
      have ha_pos' : a ≠ 0 := by omega
      have ha_mem : a ∈ Nat.divisors 21 := by
        apply Nat.mem_divisors.mpr
        omega
      have h_divisors : Nat.divisors 21 = {1, 3, 7, 21} := by
        decide
      rw [h_divisors] at ha_mem
      simpa using ha_mem
    rw [hm, hn]
    rcases h_cases with (rfl|rfl|rfl|rfl)
    · rw [one_mul] at hab
      rw [hab]
      norm_num
    · have hb : b = 7 := by
        zify at hab
        nlinarith
      rw [hb]
    · have hb : b = 3 := by
        zify at hab
        nlinarith
      rw [hb]
    · have hb : b = 1 := by
        zify at hab
        nlinarith
      rw [hb]
      norm_num
