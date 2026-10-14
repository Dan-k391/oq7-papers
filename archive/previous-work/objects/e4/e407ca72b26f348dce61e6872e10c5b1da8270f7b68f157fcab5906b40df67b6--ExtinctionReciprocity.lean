import work.ReciprocityL2
import PrescribedExtinction.MaterialVolumeUniqueness
import PrescribedExtinction.PhysicalExtinctionWork
import Mathlib.LinearAlgebra.Matrix.Symmetric

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem tensor_bilinear_reciprocity (T : Tensor) (hT : T.transpose = T) (u v : Vector) :
    bilinear (tensorApply T u) v = bilinear (tensorApply T v) u := by
  rw [bilinear_comm, bilinear_comm (tensorApply T v) u]
  change dotProduct (WithLp.ofLp v) (T.mulVec (WithLp.ofLp u)) = dotProduct (WithLp.ofLp u) (T.mulVec (WithLp.ofLp v))
  exact (show T.IsSymm from hT).dotProduct_mulVec_comm

theorem bodySusceptibility_reciprocal (B : TwoLayerBody)
    (ha : B.absorberPermittivity.transpose = B.absorberPermittivity)
    (hb : B.platePermittivity.transpose = B.platePermittivity) (x : Position) :
    (B.susceptibility x).transpose = B.susceptibility x := by
  classical
  unfold TwoLayerBody.susceptibility TwoLayerBody.permittivity
  split_ifs <;> simp [Matrix.transpose_sub, ha, hb]

theorem incidentElectric_norm (k : ℝ) (σ : Direction) (x : Position) : ‖incidentElectric k σ x‖ = 1 := by
  nlinarith [incidentElectric_squareNorm k σ x, squareNorm_eq_norm_sq (incidentElectric k σ x),
    norm_nonneg (incidentElectric k σ x)]

theorem compactCurrent_incident_bilinear_integrable (k : ℝ) (σ : Direction) (p : CompactPolarization) :
    Integrable (fun x => bilinear (p.current x) (incidentElectric k σ x)) volume := by
  have hm : AEStronglyMeasurable (fun x => bilinear (p.current x) (incidentElectric k σ x)) volume := by
    simp_rw [bilinear_eq_conjugate_inner]
    exact (vectorConjugateCLM.continuous.comp_aestronglyMeasurable p.memLp.aestronglyMeasurable).inner
      (incidentElectric_contDiff k σ).continuous.aestronglyMeasurable
  apply (compactPolarization_current_integrable p).norm.mono' hm
  exact ae_of_all _ (fun x => by simpa only [incidentElectric_norm, mul_one] using bilinear_norm_le (p.current x) (incidentElectric k σ x))

theorem volumeExtinction_global_current_work (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p) :
    extinction k B σ (volumeTotalElectric k σ p) =
      k * (∫ x : Position, pairing (incidentElectric k σ x) (p.current x)).im := by
  rw [volumeExtinction_current_work k B σ p hp]
  congr 2
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [materialVolumeCurrent_supported k B σ p hp] with x hx
  intro hxd
  simp [hx hxd, pairing]

theorem reciprocalMaterialVolume_incident_work (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (ha : B.absorberPermittivity.transpose = B.absorberPermittivity)
    (hb : B.platePermittivity.transpose = B.platePermittivity)
    (p q : CompactPolarization) (hp : MaterialVolumeEquation k B .plus p)
    (hq : MaterialVolumeEquation k B .minus q) :
    (∫ x : Position, bilinear (p.current x) (incidentElectric k .minus x)) =
      ∫ x : Position, bilinear (q.current x) (incidentElectric k .plus x) := by
  have hpoint : (fun x => bilinear (p.current x) (incidentElectric k .minus x) -
      bilinear (q.current x) (incidentElectric k .plus x)) =ᵐ[volume]
      (fun x => bilinear (q.current x) (electricVolumeField k p x) -
        bilinear (p.current x) (electricVolumeField k q x)) := by
    filter_upwards [hp, hq, outgoingElectricField_eq_ae k p, outgoingElectricField_eq_ae k q] with x hxp hxq hep heq
    have hc : bilinear (p.current x) (volumeTotalElectric k .minus q x) =
        bilinear (q.current x) (volumeTotalElectric k .plus p x) := by
      rw [hxp, hxq]
      exact tensor_bilinear_reciprocity (B.susceptibility x) (bodySusceptibility_reciprocal B ha hb x) _ _
    simp only [volumeTotalElectric, hep, heq, bilinear_add_right] at hc
    linear_combination hc
  have he := integral_congr_ae hpoint
  rw [integral_sub (compactCurrent_incident_bilinear_integrable k .minus p)
    (compactCurrent_incident_bilinear_integrable k .plus q),
    integral_sub (compactCurrents_bilinear_volume_integrable k q p) (compactCurrents_bilinear_volume_integrable k p q),
    physicalOutgoingVolume_reciprocity k hk q p, sub_self] at he
  exact sub_eq_zero.mp he

/-- Equal original physical extinction for the two opposite unit incident
waves in the same actual reciprocal body. -/
theorem physicalVolume_extinction_reciprocity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (ha : B.absorberPermittivity.transpose = B.absorberPermittivity)
    (hb : B.platePermittivity.transpose = B.platePermittivity)
    (p q : CompactPolarization) (hp : MaterialVolumeEquation k B .plus p)
    (hq : MaterialVolumeEquation k B .minus q) :
    extinction k B .plus (volumeTotalElectric k .plus p) =
      extinction k B .minus (volumeTotalElectric k .minus q) := by
  rw [volumeExtinction_global_current_work k B .plus p hp, volumeExtinction_global_current_work k B .minus q hq]
  have he := reciprocalMaterialVolume_incident_work k hk B ha hb p q hp hq
  have hplus (x : Position) : bilinear (p.current x) (incidentElectric k .minus x) =
      pairing (incidentElectric k .plus x) (p.current x) := by
    rw [incidentElectric_minus_conjugate]
    exact bilinear_vectorConjugate_right _ _
  have hminus (x : Position) : bilinear (q.current x) (incidentElectric k .plus x) =
      pairing (incidentElectric k .minus x) (q.current x) := by
    rw [incidentElectric_minus_conjugate]
    simp [bilinear, pairing, vectorConjugate_apply, mul_comm]
  simp_rw [hplus, hminus] at he
  rw [he]

end OQ7Prescribed
