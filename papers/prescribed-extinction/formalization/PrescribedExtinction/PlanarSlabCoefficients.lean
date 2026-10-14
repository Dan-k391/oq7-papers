import OQ7.StrictLoss
import PrescribedExtinction.PlanarLayerIncoming

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open scoped Matrix

def dielectricSlab (p q d : ℝ) : OQ7.HomogeneousLayer := ⟨p, q, d⟩
def dielectricSlabReflection (k p q d : ℝ) : ℂ :=
  OQ7.transferReflectionLeft (OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d)))
def dielectricSlabTransmission (k p q d : ℝ) : ℂ :=
  OQ7.transferTransmissionRight (OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d)))

theorem homogeneousWaveTransfer_offdiagonal (k d : ℝ) (n : ℂ) :
    OQ7.waveTransfer (OQ7.homogeneousTransfer k n d) 1 0 =
      -OQ7.waveTransfer (OQ7.homogeneousTransfer k n d) 0 1 := by
  simp [OQ7.waveTransfer, OQ7.waveBasis, OQ7.waveBasisInv, OQ7.homogeneousTransfer,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem dielectricSlabReflection_both_sides (k p q d : ℝ) :
    OQ7.transferReflectionRight (OQ7.waveTransfer (OQ7.layerTransfer k (dielectricSlab p q d))) =
      dielectricSlabReflection k p q d := by
  unfold dielectricSlabReflection OQ7.transferReflectionLeft OQ7.transferReflectionRight OQ7.layerTransfer
  rw [homogeneousWaveTransfer_offdiagonal, neg_neg]

theorem dielectricSlab_passive (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    OQ7.Passive (dielectricSlabReflection k p q d) (dielectricSlabReflection k p q d)
      (dielectricSlabTransmission k p q d) := by
  have hl : OQ7.LayerAdmissible p q (dielectricSlab p q d) := ⟨hp, le_rfl, hq, le_rfl, hd⟩
  have hflux := OQ7.layerTransfer_fluxDefect_posSemidef hk.le (layer := dielectricSlab p q d) hp hq hd
  have he := OQ7.passive_transfer_scattering _ hflux (OQ7.layerTransfer_det k hl)
  rw [dielectricSlabReflection_both_sides] at he
  exact he

theorem dielectricSlabTransmission_ne_zero (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) : dielectricSlabTransmission k p q d ≠ 0 :=
  OQ7.passive_transfer_transmission_ne_zero _
    (OQ7.layerTransfer_fluxDefect_posSemidef hk.le (layer := dielectricSlab p q d) hp hq hd)

theorem dielectricSlabReflection_normSq_lt_one (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) : Complex.normSq (dielectricSlabReflection k p q d) < 1 := by
  have ha := (OQ7.passive_absorptances_nonneg (dielectricSlab_passive k hk p q d hp hq hd)).1
  have ht := Complex.normSq_pos.mpr (dielectricSlabTransmission_ne_zero k hk p q d hp hq hd)
  unfold OQ7.absorptanceLeft at ha
  linarith

theorem dielectricSlab_absorptance_lt_one (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    OQ7.absorptanceLeft (dielectricSlabReflection k p q d) (dielectricSlabTransmission k p q d) < 1 := by
  have ht := Complex.normSq_pos.mpr (dielectricSlabTransmission_ne_zero k hk p q d hp hq hd)
  have hr := Complex.normSq_nonneg (dielectricSlabReflection k p q d)
  unfold OQ7.absorptanceLeft
  linarith

theorem dielectricSlab_field_boundary (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    OQ7.layerElectricField k (dielectricSlab p q d)
      (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) d =
        dielectricSlabTransmission k p q d ∧
    OQ7.layerMagneticField k (dielectricSlab p q d)
      (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) d =
        dielectricSlabTransmission k p q d := by
  have hl : OQ7.LayerAdmissible p q (dielectricSlab p q d) := ⟨hp, le_rfl, hq, le_rfl, hd⟩
  have hden := OQ7.passive_transfer_denominator_ne_zero _
    (OQ7.layerTransfer_fluxDefect_posSemidef hk.le (layer := dielectricSlab p q d) hp hq hd)
  have hb := OQ7.field_transfer_boundary_states _ hden (OQ7.layerTransfer_det k hl)
  have he0 := congrArg (fun M : OQ7.Mat2 => M 0 0) hb
  have he1 := congrArg (fun M : OQ7.Mat2 => M 1 0) hb
  have hf := OQ7.layerField_transfer_boundary k (dielectricSlab p q d)
    (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d)
  have hf0 := congrArg (fun v : Fin 2 → ℂ => v 0) hf
  have hf1 := congrArg (fun v : Fin 2 → ℂ => v 1) hf
  simp [OQ7.inputFieldStates, OQ7.outputFieldStates, Matrix.mul_apply, Fin.sum_univ_two] at he0 he1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hf0 hf1
  constructor
  · exact hf0.symm.trans he0
  · exact hf1.symm.trans he1

end OQ7Prescribed
