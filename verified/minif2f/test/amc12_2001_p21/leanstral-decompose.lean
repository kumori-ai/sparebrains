import Mathlib

open scoped Nat
open scoped Real

/--
Four positive integers $ a,b,c,$ and $ d$ have a product of 8! and satisfy\begin{align*}ab +{} a +{} b &={} 524\\
bc +{} b +{} c &={} 146\\
cd +{} c +{} d &={} 104.\end{align*} What is $ a -{} d$?

$ \textbf{(A)} \ 4 \qquad \textbf{(B)} \ 6 \qquad \textbf{(C)} \ 8 \qquad \textbf{(D)} \ 10 \qquad \textbf{(E)} \ 12$ -/
theorem amc12_2001_p21 (a b c d : ℕ) (h₀ : a * b * c * d = 8!) (h₁ : a * b + a + b = 524)
    (h₂ : b * c + b + c = 146) (h₃ : c * d + c + d = 104) : ↑a - ↑d = (10 : ℤ) := by
  push_cast at h₀ h₁ h₂ h₃
  have h1_eq : ((a : ℤ) + 1) * ((b : ℤ) + 1) = 525 := by
    nlinarith
  have h2_eq : ((b : ℤ) + 1) * ((c : ℤ) + 1) = 147 := by
    nlinarith
  have h3_eq : ((c : ℤ) + 1) * ((d : ℤ) + 1) = 105 := by
    nlinarith
  have ha1_dvd_525_nat : (a + 1 : ℕ) ∣ 525 := by
    have h1_eq_nat : (a + 1 : ℕ) * (b + 1 : ℕ) = 525 := by exact_mod_cast h1_eq
    rw [← h1_eq_nat]
    exact ⟨b + 1, rfl⟩
  have hb1_dvd_525_nat : (b + 1 : ℕ) ∣ 525 := by
    have h1_eq_nat : (a + 1 : ℕ) * (b + 1 : ℕ) = 525 := by exact_mod_cast h1_eq
    rw [← h1_eq_nat]
    exact ⟨a + 1, mul_comm _ _⟩
  have hb1_dvd_147_nat : (b + 1 : ℕ) ∣ 147 := by
    have h2_eq_nat : (b + 1 : ℕ) * (c + 1 : ℕ) = 147 := by exact_mod_cast h2_eq
    rw [← h2_eq_nat]
    exact ⟨c + 1, rfl⟩
  have hb1_dvd_21_nat : (b + 1 : ℕ) ∣ 21 := by
    have h_gcd : Nat.gcd 525 147 = 21 := by norm_num
    have h := Nat.dvd_gcd hb1_dvd_525_nat hb1_dvd_147_nat
    rwa [h_gcd] at h
  have hb1_mem : b + 1 ∈ Nat.divisors 21 := by
    rw [Nat.mem_divisors]
    exact ⟨hb1_dvd_21_nat, by norm_num⟩
  have divisors_21_eq : Nat.divisors 21 = {1, 3, 7, 21} := by
    decide
  rw [divisors_21_eq] at hb1_mem
  have hb_cases : b + 1 = 1 ∨ b + 1 = 3 ∨ b + 1 = 7 ∨ b + 1 = 21 := by
    simpa using hb1_mem
  rcases hb_cases with (hb1_eq | hb1_eq | hb1_eq | hb1_eq)
  · -- b + 1 = 1
    have hb0 : b = 0 := by omega
    subst hb0
    push_cast at h₁ h₂ h₃
    omega
  · -- b + 1 = 3
    have hb2 : b = 2 := by omega
    subst hb2
    push_cast at h₁ h₂ h₃
    grind
  · -- b + 1 = 7
    have hb6 : b = 6 := by omega
    subst hb6
    push_cast at h₁ h₂ h₃
    have ha : (a : ℤ) = 74 := by omega
    have hc : (c : ℤ) = 20 := by omega
    have hd : (d : ℤ) = 4 := by
      nlinarith
    have ha_nat : a = 74 := by exact_mod_cast ha
    have hc_nat : c = 20 := by exact_mod_cast hc
    have hd_nat : d = 4 := by exact_mod_cast hd
    rw [ha_nat, hc_nat, hd_nat] at h₀
    norm_num at h₀
  · -- b + 1 = 21
    have hb20 : b = 20 := by omega
    subst hb20
    push_cast at h₁ h₂ h₃
    have ha : (a : ℤ) = 24 := by omega
    have hc : (c : ℤ) = 6 := by omega
    have hd : (d : ℤ) = 14 := by
      nlinarith
    rw [ha, hd]
    norm_num
