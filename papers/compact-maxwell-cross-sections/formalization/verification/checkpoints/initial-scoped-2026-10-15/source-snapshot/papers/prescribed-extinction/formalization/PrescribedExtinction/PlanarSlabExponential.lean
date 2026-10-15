import OQ7.Layers
import OQ7.Transfer
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace OQ7Prescribed

def slabPropagation (k : ℝ) (n : ℂ) (d : ℝ) : ℂ :=
  Complex.exp (((k : ℂ) * n * (d : ℂ)) * Complex.I)
def slabInterfaceReflection (n : ℂ) : ℂ := (1 - n) / (1 + n)

theorem slabPropagation_ne_zero (k : ℝ) (n : ℂ) (d : ℝ) : slabPropagation k n d ≠ 0 :=
  Complex.exp_ne_zero _

theorem homogeneousWaveTransfer_11_exponential (k d : ℝ) (n : ℂ) (hn : n ≠ 0) :
    OQ7.waveTransfer (OQ7.homogeneousTransfer k n d) 1 1 =
      ((1 + n) ^ 2 - (1 - n) ^ 2 * slabPropagation k n d ^ 2) /
        (4 * n * slabPropagation k n d) := by
  simp [OQ7.waveTransfer, OQ7.waveBasis, OQ7.waveBasisInv, OQ7.homogeneousTransfer,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.cos, Complex.sin, neg_mul, Complex.exp_neg,
    slabPropagation]
  field_simp [hn, Complex.exp_ne_zero]
  ring_nf
  simp [Complex.I_sq] <;> ring

theorem homogeneousWaveTransfer_10_exponential (k d : ℝ) (n : ℂ) (hn : n ≠ 0) :
    OQ7.waveTransfer (OQ7.homogeneousTransfer k n d) 1 0 =
      (1 - n ^ 2) * (slabPropagation k n d ^ 2 - 1) /
        (4 * n * slabPropagation k n d) := by
  simp [OQ7.waveTransfer, OQ7.waveBasis, OQ7.waveBasisInv, OQ7.homogeneousTransfer,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.cos, Complex.sin, neg_mul, Complex.exp_neg,
    slabPropagation]
  field_simp [hn, Complex.exp_ne_zero]
  ring_nf
  simp [Complex.I_sq] <;> ring

theorem homogeneousSlabReflection_interface_formula (k d : ℝ) (n : ℂ) (hn : n ≠ 0)
    (hnp : 1 + n ≠ 0) :
    OQ7.transferReflectionLeft (OQ7.waveTransfer (OQ7.homogeneousTransfer k n d)) =
      slabInterfaceReflection n * (1 - slabPropagation k n d ^ 2) /
        (1 - slabInterfaceReflection n ^ 2 * slabPropagation k n d ^ 2) := by
  rw [OQ7.transferReflectionLeft, homogeneousWaveTransfer_10_exponential k d n hn,
    homogeneousWaveTransfer_11_exponential k d n hn]
  unfold slabInterfaceReflection
  rw [← neg_div, div_div_div_cancel_right₀
    (mul_ne_zero (mul_ne_zero (by norm_num) hn) (slabPropagation_ne_zero k n d))]
  by_cases hD : (1 + n) ^ 2 - (1 - n) ^ 2 * slabPropagation k n d ^ 2 = 0
  · have hz : 1 - ((1 - n) / (1 + n)) ^ 2 * slabPropagation k n d ^ 2 = 0 := by
      field_simp
      linear_combination hD
    simp [hD, hz]
  · field_simp
    ring

theorem homogeneousSlabTransmission_interface_formula (k d : ℝ) (n : ℂ) (hn : n ≠ 0)
    (hnp : 1 + n ≠ 0) :
    OQ7.transferTransmissionRight (OQ7.waveTransfer (OQ7.homogeneousTransfer k n d)) =
      (1 - slabInterfaceReflection n ^ 2) * slabPropagation k n d /
        (1 - slabInterfaceReflection n ^ 2 * slabPropagation k n d ^ 2) := by
  rw [OQ7.transferTransmissionRight, homogeneousWaveTransfer_11_exponential k d n hn, one_div_div]
  unfold slabInterfaceReflection
  by_cases hD : (1 + n) ^ 2 - (1 - n) ^ 2 * slabPropagation k n d ^ 2 = 0
  · have hz : 1 - ((1 - n) / (1 + n)) ^ 2 * slabPropagation k n d ^ 2 = 0 := by
      field_simp
      linear_combination hD
    rw [hD, hz, div_zero, div_zero]
  · field_simp
    ring

end OQ7Prescribed
