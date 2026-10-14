import PrescribedExtinction.PlanarLosslessPlate
import PrescribedExtinction.PlanarDielectricIndex
import PrescribedExtinction.PlanarSlabCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem dielectricSlabIndex_real_square (n : ℝ) (hn : 0 < n) :
    dielectricSlabIndex (n ^ 2) 0 = (n : ℂ) := by
  have hs : dielectricSlabIndex (n ^ 2) 0 ^ 2 = (n : ℂ) ^ 2 := by
    rw [dielectricSlabIndex_sq]
    simp only [Complex.ofReal_zero, mul_zero, add_zero]
    exact Complex.ofReal_pow n 2
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · exact h
  · have hr := dielectricSlabIndex_re_pos (n ^ 2) 0 (sq_pos_of_pos hn)
    rw [h, Complex.neg_re, Complex.ofReal_re] at hr
    linarith

theorem losslessPlateDesign_actual_transfer (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j) :
    OQ7.layerTransfer k (dielectricSlab (plateDesignPermittivity j) 0 (plateDesignThickness k j)) = 1 := by
  change OQ7.homogeneousTransfer k (dielectricSlabIndex ((plateDesignIndex j) ^ 2) 0) _ = _
  rw [dielectricSlabIndex_real_square _ (by linarith [plateDesignIndex_gt_one j hj])]
  exact losslessPlateDesign_active_transfer k hk j hj

theorem losslessPlateDesign_actual_coefficients (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j) :
    dielectricSlabReflection k (plateDesignPermittivity j) 0 (plateDesignThickness k j) = 0 ∧
    dielectricSlabTransmission k (plateDesignPermittivity j) 0 (plateDesignThickness k j) = 1 := by
  unfold dielectricSlabReflection dielectricSlabTransmission
  rw [losslessPlateDesign_actual_transfer k hk j hj]
  norm_num [OQ7.waveTransfer, OQ7.waveBasisInv, OQ7.waveBasis, OQ7.transferReflectionLeft,
    OQ7.transferTransmissionRight, Matrix.mul_apply, Fin.sum_univ_two]

theorem losslessPlateDesign_vacuum_phase (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j) :
    apertureOscillation k (plateDesignThickness k j) = -1 := by
  have hp := (plateDesign_phases k hk.ne' j hj).1
  have hpc : ((k * plateDesignThickness k j : ℝ) : ℂ) =
      (j : ℂ) * (2 * (Real.pi : ℂ)) - (Real.pi : ℂ) := by exact_mod_cast hp
  unfold apertureOscillation
  rw [mul_comm Complex.I, Complex.exp_mul_I, hpc]
  simp [Complex.cos_nat_mul_two_pi_sub_pi, Complex.sin_nat_mul_two_pi_sub]

end OQ7Prescribed
