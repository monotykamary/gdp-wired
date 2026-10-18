example (g d c c' : Int) (hg : 1 ≤ g) (h : g * d + c ≤ 0) (hc : g * c' ≤ c + g - 1) : d + c' ≤ 0 := by
  have hd : g * (d + c') = g * d + g * c' := Int.mul_add g d c'
  refine Int.not_lt.mp (fun h1 => ?_)
  have h2 : g * 1 ≤ g * (d + c') := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega
