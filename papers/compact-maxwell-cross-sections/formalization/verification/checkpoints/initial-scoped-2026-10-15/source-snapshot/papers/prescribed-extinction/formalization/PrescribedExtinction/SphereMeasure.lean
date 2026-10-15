import PrescribedExtinction.NewtonKernel
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The actual angular measure and its orthogonal invariance, needed for the
Newtonian contact boundary term. No punctured integration identity is assumed. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Metric
open scoped Pointwise

abbrev UnitSphere := sphere (0 : Position) 1
def sphereArea : Measure UnitSphere := (volume : Measure Position).toSphere

instance sphereArea_finite : IsFiniteMeasure sphereArea := by
  unfold sphereArea
  infer_instance

theorem unitSphere_norm (n : UnitSphere) : ‖(n : Position)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using n.property

def orthogonalSphere (e : Position ≃ₗᵢ[ℝ] Position) : UnitSphere ≃ₜ UnitSphere where
  toFun n := ⟨e n, by simpa only [mem_sphere, dist_zero_right, e.norm_map] using unitSphere_norm n⟩
  invFun n := ⟨e.symm n, by simpa only [mem_sphere, dist_zero_right, e.symm.norm_map] using unitSphere_norm n⟩
  left_inv n := Subtype.ext (e.symm_apply_apply n)
  right_inv n := Subtype.ext (e.apply_symm_apply n)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sphereArea_real_univ : sphereArea.real univ = 4 * Real.pi := by
  unfold sphereArea
  rw [Measure.toSphere_real_apply_univ]
  simp only [Position, finrank_euclideanSpace_fin,
    measureReal_def, EuclideanSpace.volume_ball_fin_three]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem orthogonalSphere_cone_preimage (e : Position ≃ₗᵢ[ℝ] Position) (s : Set UnitSphere) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((orthogonalSphere e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, e n, ⟨orthogonalSphere e n, hn, rfl⟩, (e.map_smul r n).symm⟩
  · rintro ⟨r, hr, y, ⟨n, hn, rfl⟩, hx⟩
    refine ⟨r, hr, e.symm n, ⟨(orthogonalSphere e).symm n, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hn
    · have h := congrArg e.symm hx
      simpa only [e.symm.map_smul, e.symm_apply_apply] using h

theorem orthogonalSphere_measurePreserving (e : Position ≃ₗᵢ[ℝ] Position) :
    MeasurePreserving (orthogonalSphere e) sphereArea sphereArea := by
  refine ⟨(orthogonalSphere e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (orthogonalSphere e).measurable hs]
  unfold sphereArea
  rw [Measure.toSphere_apply' _ ((orthogonalSphere e).measurable hs),
    Measure.toSphere_apply' _ hs, orthogonalSphere_cone_preimage]
  congr 1
  exact e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding _

theorem sphere_integral_orthogonal (e : Position ≃ₗᵢ[ℝ] Position) (f : UnitSphere → ℝ) :
    (∫ n, f (orthogonalSphere e n) ∂sphereArea) = ∫ n, f n ∂sphereArea :=
  (orthogonalSphere_measurePreserving e).integral_comp'
    (f := (orthogonalSphere e).toMeasurableEquiv) f

end OQ7Prescribed
