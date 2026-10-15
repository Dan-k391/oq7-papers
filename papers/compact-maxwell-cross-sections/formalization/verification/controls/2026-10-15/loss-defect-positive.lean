import CompactMaxwell.SixVectorEquality
open scoped ComplexOrder
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (Q (A 0 (Real.sqrt (1/2)))).PosSemidef := by
  apply passive
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num
