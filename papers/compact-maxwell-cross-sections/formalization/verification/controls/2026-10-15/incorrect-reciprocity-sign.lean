import CompactMaxwell.SixVectorEquality
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (A 0 1).transpose = A 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, M]
