import FixedResource.SphereAlgebra
open scoped Matrix
open FixedResource.SphereAlgebra
example : ((power (L *ᵥ plus) - power (L *ᵥ minus)) / 2) / ((quad L plus).im / 2) = (721 : ℝ) / 2071 := by
  rw [normalized_coefficient.1]
  norm_num
