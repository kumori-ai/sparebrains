import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown (m n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ x, f x = 4 ^ x + 6 ^ x + 9 ^ x) (h₁ : 0 < m ∧ 0 < n) (h₂ : m ≤ n) :
    f (2 ^ m) ∣ f (2 ^ n) := by
  obtain ⟨hm, hn⟩ := h₁
  set a := 2 ^ m with ha
  set X : ℕ := 2 ^ a with hX
  set Y : ℕ := 3 ^ a with hY
  have h4 : (4 : ℕ) ^ a = X ^ 2 := by
    calc (4 : ℕ) ^ a = (2 ^ 2) ^ a := by norm_num
      _ = 2 ^ (2 * a) := by rw [← pow_mul]
      _ = 2 ^ (a * 2) := by rw [mul_comm]
      _ = (2 ^ a) ^ 2 := by rw [pow_mul]
      _ = X ^ 2 := by rw [hX]
  have h9 : (9 : ℕ) ^ a = Y ^ 2 := by
    calc (9 : ℕ) ^ a = (3 ^ 2) ^ a := by norm_num
      _ = 3 ^ (2 * a) := by rw [← pow_mul]
      _ = 3 ^ (a * 2) := by rw [mul_comm]
      _ = (3 ^ a) ^ 2 := by rw [pow_mul]
      _ = Y ^ 2 := by rw [hY]
  have h6 : (6 : ℕ) ^ a = X * Y := by
    calc (6 : ℕ) ^ a = (2 * 3) ^ a := by norm_num
      _ = 2 ^ a * 3 ^ a := by rw [mul_pow]
      _ = X * Y := by rw [hX, hY]
  have hf_a : f a = X ^ 2 + X * Y + Y ^ 2 := by
    rw [h₀, h4, h6, h9]
  have h2n : 2 ^ n = a * 2 ^ (n - m) := by
    calc 2 ^ n = 2 ^ (m + (n - m)) := congrArg (fun k => 2 ^ k) (Nat.add_sub_of_le h₂).symm
      _ = 2 ^ m * 2 ^ (n - m) := by rw [pow_add]
      _ = a * 2 ^ (n - m) := by rw [ha]
  have e4 : (4 : ℕ) ^ (a * 2 ^ (n - m)) = (X ^ (2 ^ (n - m))) ^ 2 := by
    calc (4 : ℕ) ^ (a * 2 ^ (n - m)) = ((4 : ℕ) ^ a) ^ (2 ^ (n - m)) := by rw [pow_mul]
      _ = (X ^ 2) ^ (2 ^ (n - m)) := by rw [h4]
      _ = X ^ (2 * 2 ^ (n - m)) := by rw [← pow_mul]
      _ = X ^ (2 ^ (n - m) * 2) := by rw [mul_comm]
      _ = (X ^ (2 ^ (n - m))) ^ 2 := by rw [pow_mul]
  have e9 : (9 : ℕ) ^ (a * 2 ^ (n - m)) = (Y ^ (2 ^ (n - m))) ^ 2 := by
    calc (9 : ℕ) ^ (a * 2 ^ (n - m)) = ((9 : ℕ) ^ a) ^ (2 ^ (n - m)) := by rw [pow_mul]
      _ = (Y ^ 2) ^ (2 ^ (n - m)) := by rw [h9]
      _ = Y ^ (2 * 2 ^ (n - m)) := by rw [← pow_mul]
      _ = Y ^ (2 ^ (n - m) * 2) := by rw [mul_comm]
      _ = (Y ^ (2 ^ (n - m))) ^ 2 := by rw [pow_mul]
  have e6 : (6 : ℕ) ^ (a * 2 ^ (n - m)) = X ^ (2 ^ (n - m)) * Y ^ (2 ^ (n - m)) := by
    calc (6 : ℕ) ^ (a * 2 ^ (n - m)) = ((6 : ℕ) ^ a) ^ (2 ^ (n - m)) := by rw [pow_mul]
      _ = (X * Y) ^ (2 ^ (n - m)) := by rw [h6]
      _ = X ^ (2 ^ (n - m)) * Y ^ (2 ^ (n - m)) := by rw [mul_pow]
  have hf_n : f (2 ^ n) = (X ^ (2 ^ (n - m))) ^ 2 + X ^ (2 ^ (n - m)) * Y ^ (2 ^ (n - m)) + (Y ^ (2 ^ (n - m))) ^ 2 := by
    rw [h₀, h2n, e4, e6, e9]
  have key : ∀ s : ℕ, ((X : ℤ) ^ 2 + (X : ℤ) * (Y : ℤ) + (Y : ℤ) ^ 2) ∣
      ((X : ℤ) ^ (2 ^ s)) ^ 2 + (X : ℤ) ^ (2 ^ s) * (Y : ℤ) ^ (2 ^ s) + ((Y : ℤ) ^ (2 ^ s)) ^ 2 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hexp : 2 ^ (s + 1) = 2 ^ s * 2 := pow_succ 2 s
      have e1 : (X : ℤ) ^ (2 ^ (s + 1)) = ((X : ℤ) ^ (2 ^ s)) ^ 2 := by
        rw [hexp, pow_mul]
      have e2 : (Y : ℤ) ^ (2 ^ (s + 1)) = ((Y : ℤ) ^ (2 ^ s)) ^ 2 := by
        rw [hexp, pow_mul]
      have hfactor : ((X : ℤ) ^ (2 ^ (s + 1))) ^ 2 + (X : ℤ) ^ (2 ^ (s + 1)) * (Y : ℤ) ^ (2 ^ (s + 1)) + ((Y : ℤ) ^ (2 ^ (s + 1))) ^ 2
          = (((X : ℤ) ^ (2 ^ s)) ^ 2 + ((Y : ℤ) ^ (2 ^ s)) ^ 2 - (X : ℤ) ^ (2 ^ s) * (Y : ℤ) ^ (2 ^ s)) *
            (((X : ℤ) ^ (2 ^ s)) ^ 2 + (X : ℤ) ^ (2 ^ s) * (Y : ℤ) ^ (2 ^ s) + ((Y : ℤ) ^ (2 ^ s)) ^ 2) := by
        rw [e1, e2]; ring
      rw [hfactor]
      exact Dvd.dvd.mul_left ih _
  have hdvd_nat : (X ^ 2 + X * Y + Y ^ 2) ∣ (X ^ (2 ^ (n - m))) ^ 2 + X ^ (2 ^ (n - m)) * Y ^ (2 ^ (n - m)) + (Y ^ (2 ^ (n - m))) ^ 2 := by
    apply Int.ofNat_dvd.mp
    push_cast
    exact key (n - m)
  rw [hf_a, hf_n]
  exact hdvd_nat
