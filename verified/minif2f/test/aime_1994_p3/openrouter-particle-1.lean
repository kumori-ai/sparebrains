import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$ has the property that, for each real number $x,$ \[ f(x)+f(x-1) = x^2. \] If $f(19)=94,$ what is the remainder when $f(94)$ is divided by 1000? -/
theorem aime_1994_p3 (f : ℤ → ℤ) (h0 : ∀ x, f x + f (x - 1) = x ^ 2) (h1 : f 19 = 94) :
    f 94 % 1000 = 561 := by
  have h20 : f 20 = 306 := by
    have h := h0 20
    norm_num at h
    omega
  have h22 : f 22 = 349 := by
    have hA := h0 22
    have hB := h0 21
    norm_num at hA hB
    omega
  have h24 : f 24 = 396 := by
    have hA := h0 24
    have hB := h0 23
    norm_num at hA hB
    omega
  have h26 : f 26 = 447 := by
    have hA := h0 26
    have hB := h0 25
    norm_num at hA hB
    omega
  have h28 : f 28 = 502 := by
    have hA := h0 28
    have hB := h0 27
    norm_num at hA hB
    omega
  have h30 : f 30 = 561 := by
    have hA := h0 30
    have hB := h0 29
    norm_num at hA hB
    omega
  have h32 : f 32 = 624 := by
    have hA := h0 32
    have hB := h0 31
    norm_num at hA hB
    omega
  have h34 : f 34 = 691 := by
    have hA := h0 34
    have hB := h0 33
    norm_num at hA hB
    omega
  have h36 : f 36 = 762 := by
    have hA := h0 36
    have hB := h0 35
    norm_num at hA hB
    omega
  have h38 : f 38 = 837 := by
    have hA := h0 38
    have hB := h0 37
    norm_num at hA hB
    omega
  have h40 : f 40 = 916 := by
    have hA := h0 40
    have hB := h0 39
    norm_num at hA hB
    omega
  have h42 : f 42 = 999 := by
    have hA := h0 42
    have hB := h0 41
    norm_num at hA hB
    omega
  have h44 : f 44 = 1086 := by
    have hA := h0 44
    have hB := h0 43
    norm_num at hA hB
    omega
  have h46 : f 46 = 1177 := by
    have hA := h0 46
    have hB := h0 45
    norm_num at hA hB
    omega
  have h48 : f 48 = 1272 := by
    have hA := h0 48
    have hB := h0 47
    norm_num at hA hB
    omega
  have h50 : f 50 = 1371 := by
    have hA := h0 50
    have hB := h0 49
    norm_num at hA hB
    omega
  have h52 : f 52 = 1474 := by
    have hA := h0 52
    have hB := h0 51
    norm_num at hA hB
    omega
  have h54 : f 54 = 1581 := by
    have hA := h0 54
    have hB := h0 53
    norm_num at hA hB
    omega
  have h56 : f 56 = 1692 := by
    have hA := h0 56
    have hB := h0 55
    norm_num at hA hB
    omega
  have h58 : f 58 = 1807 := by
    have hA := h0 58
    have hB := h0 57
    norm_num at hA hB
    omega
  have h60 : f 60 = 1926 := by
    have hA := h0 60
    have hB := h0 59
    norm_num at hA hB
    omega
  have h62 : f 62 = 2049 := by
    have hA := h0 62
    have hB := h0 61
    norm_num at hA hB
    omega
  have h64 : f 64 = 2176 := by
    have hA := h0 64
    have hB := h0 63
    norm_num at hA hB
    omega
  have h66 : f 66 = 2307 := by
    have hA := h0 66
    have hB := h0 65
    norm_num at hA hB
    omega
  have h68 : f 68 = 2442 := by
    have hA := h0 68
    have hB := h0 67
    norm_num at hA hB
    omega
  have h70 : f 70 = 2581 := by
    have hA := h0 70
    have hB := h0 69
    norm_num at hA hB
    omega
  have h72 : f 72 = 2724 := by
    have hA := h0 72
    have hB := h0 71
    norm_num at hA hB
    omega
  have h74 : f 74 = 2871 := by
    have hA := h0 74
    have hB := h0 73
    norm_num at hA hB
    omega
  have h76 : f 76 = 3022 := by
    have hA := h0 76
    have hB := h0 75
    norm_num at hA hB
    omega
  have h78 : f 78 = 3177 := by
    have hA := h0 78
    have hB := h0 77
    norm_num at hA hB
    omega
  have h80 : f 80 = 3336 := by
    have hA := h0 80
    have hB := h0 79
    norm_num at hA hB
    omega
  have h82 : f 82 = 3499 := by
    have hA := h0 82
    have hB := h0 81
    norm_num at hA hB
    omega
  have h84 : f 84 = 3666 := by
    have hA := h0 84
    have hB := h0 83
    norm_num at hA hB
    omega
  have h86 : f 86 = 3837 := by
    have hA := h0 86
    have hB := h0 85
    norm_num at hA hB
    omega
  have h88 : f 88 = 4012 := by
    have hA := h0 88
    have hB := h0 87
    norm_num at hA hB
    omega
  have h90 : f 90 = 4191 := by
    have hA := h0 90
    have hB := h0 89
    norm_num at hA hB
    omega
  have h92 : f 92 = 4374 := by
    have hA := h0 92
    have hB := h0 91
    norm_num at hA hB
    omega
  have h94 : f 94 = 4561 := by
    have hA := h0 94
    have hB := h0 93
    norm_num at hA hB
    omega
  rw [h94]
  norm_num
