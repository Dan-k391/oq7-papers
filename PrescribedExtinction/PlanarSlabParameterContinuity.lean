import PrescribedExtinction.PlanarDielectricIndex
import PrescribedExtinction.PlanarSlabCoefficients
import Mathlib.Topology.Instances.Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set

theorem homogeneousTransfer_index_loss_continuous (k p d : ℝ) (hp : 0 < p) :
    Continuous (fun q : ℝ => OQ7.homogeneousTransfer k (dielectricSlabIndex p q) d) := by
  have hn := dielectricSlabIndex_loss_continuous p hp
  have hne : ∀ q : ℝ, dielectricSlabIndex p q ≠ 0 := fun q => dielectricSlabIndex_ne_zero p q hp
  have hphase : Continuous (fun q : ℝ => (k : ℂ) * dielectricSlabIndex p q * (d : ℂ)) :=
    (continuous_const.mul hn).mul continuous_const
  have hc := Complex.continuous_cos.comp hphase
  have hs := Complex.continuous_sin.comp hphase
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [OQ7.homogeneousTransfer, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact hc
  · exact (continuous_const.mul hs).div hn hne
  · exact (continuous_const.mul hn).mul hs
  · exact hc

theorem dielectricSlabWaveTransfer_loss_continuous (k p d : ℝ) (hp : 0 < p) :
    Continuous (fun q : ℝ => OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d))) := by
  change Continuous (fun q : ℝ => OQ7.waveBasisInv * OQ7.homogeneousTransfer k (dielectricSlabIndex p q) d * OQ7.waveBasis)
  exact (continuous_const.mul (homogeneousTransfer_index_loss_continuous k p d hp)).mul continuous_const

abbrev NonnegativeSlabLoss := {q : ℝ // 0 ≤ q}

theorem dielectricSlabReflection_loss_continuous (k : ℝ) (hk : 0 < k) (p d : ℝ)
    (hp : 1 ≤ p) (hd : 0 ≤ d) :
    Continuous (fun q : NonnegativeSlabLoss => dielectricSlabReflection k p q d) := by
  have hK : Continuous (fun q : NonnegativeSlabLoss => OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d))) :=
    (dielectricSlabWaveTransfer_loss_continuous k p d (by linarith)).comp continuous_subtype_val
  have hden (q : NonnegativeSlabLoss) : OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d)) 1 1 ≠ 0 :=
    OQ7.passive_transfer_denominator_ne_zero _ (OQ7.layerTransfer_fluxDefect_posSemidef hk.le hp q.property hd)
  exact (hK.matrix_elem 1 0).neg.div (hK.matrix_elem 1 1) hden

theorem dielectricSlabTransmission_loss_continuous (k : ℝ) (hk : 0 < k) (p d : ℝ)
    (hp : 1 ≤ p) (hd : 0 ≤ d) :
    Continuous (fun q : NonnegativeSlabLoss => dielectricSlabTransmission k p q d) := by
  have hK : Continuous (fun q : NonnegativeSlabLoss => OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d))) :=
    (dielectricSlabWaveTransfer_loss_continuous k p d (by linarith)).comp continuous_subtype_val
  have hden (q : NonnegativeSlabLoss) : OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d)) 1 1 ≠ 0 :=
    OQ7.passive_transfer_denominator_ne_zero _ (OQ7.layerTransfer_fluxDefect_posSemidef hk.le hp q.property hd)
  exact continuous_const.div (hK.matrix_elem 1 1) hden

theorem homogeneousElectricField_parameter_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (n E H : X → ℂ) (z : X → ℝ) (hn : Continuous n) (hE : Continuous E)
    (hH : Continuous H) (hz : Continuous z) (hne : ∀ x, n x ≠ 0) :
    Continuous (fun x => OQ7.electricField k (n x) (E x) (H x) (z x)) := by
  have hp : Continuous (fun x => (k : ℂ) * n x * (z x : ℂ)) :=
    (continuous_const.mul hn).mul (Complex.continuous_ofReal.comp hz)
  exact (hE.mul (Complex.continuous_cos.comp hp)).add
    (((continuous_const.mul hH).mul (Complex.continuous_sin.comp hp)).div hn hne)

end OQ7Prescribed
