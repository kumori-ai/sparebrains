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
  have h21 : f 21 = 135 := by
    have h := h0 21
    norm_num at h
    omega
  have h22 : f 22 = 349 := by
    have h := h0 22
    norm_num at h
    omega
  have h23 : f 23 = 180 := by
    have h := h0 23
    norm_num at h
    omega
  have h24 : f 24 = 396 := by
    have h := h0 24
    norm_num at h
    omega
  have h25 : f 25 = 229 := by
    have h := h0 25
    norm_num at h
    omega
  have h26 : f 26 = 447 := by
    have h := h0 26
    norm_num at h
    omega
  have h27 : f 27 = 282 := by
    have h := h0 27
    norm_num at h
    omega
  have h28 : f 28 = 502 := by
    have h := h0 28
    norm_num at h
    omega
  have h29 : f 29 = 339 := by
    have h := h0 29
    norm_num at h
    omega
  have h30 : f 30 = 561 := by
    have h := h0 30
    norm_num at h
    omega
  have h31 : f 31 = 400 := by
    have h := h0 31
    norm_num at h
    omega
  have h32 : f 32 = 624 := by
    have h := h0 32
    norm_num at h
    omega
  have h33 : f 33 = 465 := by
    have h := h0 33
    norm_num at h
    omega
  have h34 : f 34 = 691 := by
    have h := h0 34
    norm_num at h
    omega
  have h35 : f 35 = 534 := by
    have h := h0 35
    norm_num at h
    omega
  have h36 : f 36 = 762 := by
    have h := h0 36
    norm_num at h
    omega
  have h37 : f 37 = 607 := by
    have h := h0 37
    norm_num at h
    omega
  have h38 : f 38 = 837 := by
    have h := h0 38
    norm_num at h
    omega
  have h39 : f 39 = 684 := by
    have h := h0 39
    norm_num at h
    omega
  have h40 : f 40 = 916 := by
    have h := h0 40
    norm_num at h
    omega
  have h41 : f 41 = 765 := by
    have h := h0 41
    norm_num at h
    omega
  have h42 : f 42 = 999 := by
    have h := h0 42
    norm_num at h
    omega
  have h43 : f 43 = 850 := by
    have h := h0 43
    norm_num at h
    omega
  have h44 : f 44 = 1086 := by
    have h := h0 44
    norm_num at h
    omega
  have h45 : f 45 = 939 := by
    have h := h0 45
    norm_num at h
    omega
  have h46 : f 46 = 1177 := by
    have h := h0 46
    norm_num at h
    omega
  have h47 : f 47 = 1032 := by
    have h := h0 47
    norm_num at h
    omega
  have h48 : f 48 = 1272 := by
    have h := h0 48
    norm_num at h
    omega
  have h49 : f 49 = 1129 := by
    have h := h0 49
    norm_num at h
    omega
  have h50 : f 50 = 1371 := by
    have h := h0 50
    norm_num at h
    omega
  have h51 : f 51 = 1230 := by
    have h := h0 51
    norm_num at h
    omega
  have h52 : f 52 = 1474 := by
    have h := h0 52
    norm_num at h
    omega
  have h53 : f 53 = 1335 := by
    have h := h0 53
    norm_num at h
    omega
  have h54 : f 54 = 1581 := by
    have h := h0 54
    norm_num at h
    omega
  have h55 : f 55 = 1444 := by
    have h := h0 55
    norm_num at h
    omega
  have h56 : f 56 = 1692 := by
    have h := h0 56
    norm_num at h
    omega
  have h57 : f 57 = 1557 := by
    have h := h0 57
    norm_num at h
    omega
  have h58 : f 58 = 1807 := by
    have h := h0 58
    norm_num at h
    omega
  have h59 : f 59 = 1674 := by
    have h := h0 59
    norm_num at h
    omega
  have h60 : f 60 = 1926 := by
    have h := h0 60
    norm_num at h
    omega
  have h61 : f 61 = 1795 := by
    have h := h0 61
    norm_num at h
    omega
  have h62 : f 62 = 2049 := by
    have h := h0 62
    norm_num at h
    omega
  have h63 : f 63 = 1920 := by
    have h := h0 63
    norm_num at h
    omega
  have h64 : f 64 = 2176 := by
    have h := h0 64
    norm_num at h
    omega
  have h65 : f 65 = 2049 := by
    have h := h0 65
    norm_num at h
    omega
  have h66 : f 66 = 2307 := by
    have h := h0 66
    norm_num at h
    omega
  have h67 : f 67 = 2182 := by
    have h := h0 67
    norm_num at h
    omega
  have h68 : f 68 = 2442 := by
    have h := h0 68
    norm_num at h
    omega
  have h69 : f 69 = 2319 := by
    have h := h0 69
    norm_num at h
    omega
  have h70 : f 70 = 2581 := by
    have h := h0 70
    norm_num at h
    omega
  have h71 : f 71 = 2460 := by
    have h := h0 71
    norm_num at h
    omega
  have h72 : f 72 = 2724 := by
    have h := h0 72
    norm_num at h
    omega
  have h73 : f 73 = 2605 := by
    have h := h0 73
    norm_num at h
    omega
  have h74 : f 74 = 2871 := by
    have h := h0 74
    norm_num at h
    omega
  have h75 : f 75 = 2754 := by
    have h := h0 75
    norm_num at h
    omega
  have h76 : f 76 = 3022 := by
    have h := h0 76
    norm_num at h
    omega
  have h77 : f 77 = 2907 := by
    have h := h0 77
    norm_num at h
    omega
  have h78 : f 78 = 3177 := by
    have h := h0 78
    norm_num at h
    omega
  have h79 : f 79 = 3064 := by
    have h := h0 79
    norm_num at h
    omega
  have h80 : f 80 = 3336 := by
    have h := h0 80
    norm_num at h
    omega
  have h81 : f 81 = 3225 := by
    have h := h0 81
    norm_num at h
    omega
  have h82 : f 82 = 3499 := by
    have h := h0 82
    norm_num at h
    omega
  have h83 : f 83 = 3390 := by
    have h := h0 83
    norm_num at h
    omega
  have h84 : f 84 = 3666 := by
    have h := h0 84
    norm_num at h
    omega
  have h85 : f 85 = 3559 := by
    have h := h0 85
    norm_num at h
    omega
  have h86 : f 86 = 3837 := by
    have h := h0 86
    norm_num at h
    omega
  have h87 : f 87 = 3732 := by
    have h := h0 87
    norm_num at h
    omega
  have h88 : f 88 = 4012 := by
    have h := h0 88
    norm_num at h
    omega
  have h89 : f 89 = 3909 := by
    have h := h0 89
    norm_num at h
    omega
  have h90 : f 90 = 4191 := by
    have h := h0 90
    norm_num at h
    omega
  have h91 : f 91 = 4090 := by
    have h := h0 91
    norm_num at h
    omega
  have h92 : f 92 = 4374 := by
    have h := h0 92
    norm_num at h
    omega
  have h93 : f 93 = 4275 := by
    have h := h0 93
    norm_num at h
    omega
  have h94 : f 94 = 4561 := by
    have h := h0 94
    norm_num at h
    omega
  rw [h94]
  norm_num
