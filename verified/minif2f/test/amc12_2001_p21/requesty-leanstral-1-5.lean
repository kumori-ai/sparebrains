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
  -- 8! = 40320
  have h8 : 8! = 40320 := by norm_num
  rw [h8] at h₀
  -- (a+1)(b+1) = 525, etc.
  have h1_eq : (a + 1) * (b + 1) = 525 := by
    calc
      (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
      _ = 524 + 1 := by rw [h₁]
      _ = 525 := by norm_num
  have h2_eq : (b + 1) * (c + 1) = 147 := by
    calc
      (b + 1) * (c + 1) = b * c + b + c + 1 := by ring
      _ = 146 + 1 := by rw [h₂]
      _ = 147 := by norm_num
  have h3_eq : (c + 1) * (d + 1) = 105 := by
    calc
      (c + 1) * (d + 1) = c * d + c + d + 1 := by ring
      _ = 104 + 1 := by rw [h₃]
      _ = 105 := by norm_num
  -- Divisibility conditions
  have ha_dvd : a + 1 ∣ 525 := by
    rw [← h1_eq]
    exact dvd_mul_right _ _
  have hb_dvd_525 : b + 1 ∣ 525 := by
    rw [← h1_eq]
    exact dvd_mul_left _ _
  have hb_dvd_147 : b + 1 ∣ 147 := by
    rw [← h2_eq]
    exact dvd_mul_right _ _
  have hb_dvd_21 : b + 1 ∣ 21 := by
    have hgcd : Nat.gcd 525 147 = 21 := by norm_num
    have htemp : b + 1 ∣ Nat.gcd 525 147 := Nat.dvd_gcd hb_dvd_525 hb_dvd_147
    rw [hgcd] at htemp
    exact htemp
  have hc_dvd_147 : c + 1 ∣ 147 := by
    rw [← h2_eq]
    exact dvd_mul_left _ _
  have hc_dvd_105 : c + 1 ∣ 105 := by
    rw [← h3_eq]
    exact dvd_mul_right _ _
  have hc_dvd_21 : c + 1 ∣ 21 := by
    have hgcd : Nat.gcd 147 105 = 21 := by norm_num
    have htemp : c + 1 ∣ Nat.gcd 147 105 := Nat.dvd_gcd hc_dvd_147 hc_dvd_105
    rw [hgcd] at htemp
    exact htemp
  have hd_dvd_105 : d + 1 ∣ 105 := by
    rw [← h3_eq]
    exact dvd_mul_left _ _
  -- Finsets of divisors
  let divs_525 : Finset ℕ := Nat.divisors 525
  let divs_21 : Finset ℕ := Nat.divisors 21
  let divs_105 : Finset ℕ := Nat.divisors 105
  have ha_mem : a + 1 ∈ divs_525 := by
    rw [Nat.mem_divisors]
    exact ⟨ha_dvd, by norm_num⟩
  have hb_mem : b + 1 ∈ divs_21 := by
    rw [Nat.mem_divisors]
    exact ⟨hb_dvd_21, by norm_num⟩
  have hc_mem : c + 1 ∈ divs_21 := by
    rw [Nat.mem_divisors]
    exact ⟨hc_dvd_21, by norm_num⟩
  have hd_mem : d + 1 ∈ divs_105 := by
    rw [Nat.mem_divisors]
    exact ⟨hd_dvd_105, by norm_num⟩
  -- Candidates
  let candidates : Finset (ℕ × ℕ × ℕ × ℕ) :=
    Finset.product divs_525 (Finset.product divs_21 (Finset.product divs_21 divs_105))
  let good : Finset (ℕ × ℕ × ℕ × ℕ) :=
    candidates.filter (λ ⟨x, y, z, w⟩ =>
      x * y = 525 ∧ y * z = 147 ∧ z * w = 105 ∧ (x - 1) * (y - 1) * (z - 1) * (w - 1) = 40320)
  have hgood : (a + 1, b + 1, c + 1, d + 1) ∈ good := by
    dsimp [good, candidates]
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨ha_mem, Finset.mem_product.mpr ⟨hb_mem, Finset.mem_product.mpr ⟨hc_mem, hd_mem⟩⟩⟩
    · exact ⟨h1_eq, h2_eq, h3_eq, h₀⟩
  set_option maxRecDepth 1000000 in
  have h_all : ∀ x ∈ good, (x.1 : ℤ) - (x.2.2.2 : ℤ) = (10 : ℤ) := by
    decide
  have h_result : ((a + 1 : ℕ) : ℤ) - ((d + 1 : ℕ) : ℤ) = (10 : ℤ) :=
    h_all (a + 1, b + 1, c + 1, d + 1) hgood
  -- simplify (a+1) - (d+1) = a - d
  have h_final : (a : ℤ) - (d : ℤ) = (10 : ℤ) := by
    have h' : ((a : ℤ) + 1) - ((d : ℤ) + 1) = 10 := by
      simpa [Nat.cast_add, Nat.cast_one] using h_result
    linarith
  exact h_final
