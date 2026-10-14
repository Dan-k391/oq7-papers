import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
-- deliberately wrong constant: the manuscript value is 21/2000
theorem wrong_remainder : (7 : ℝ) * (12 / 8000) = 22 / 2000 := by norm_num
