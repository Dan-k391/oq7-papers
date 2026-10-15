import CompactMaxwell.SixVectorEquality
open scoped ComplexOrder
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (Q (A 0 2)).PosSemidef := by
  apply passive
  norm_num
