import PrescribedExtinction.FarFieldKernel
import PrescribedExtinction.PhysicalExtinctionWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem realDot_eq_inner (n y : Position) : realDot n y = inner ℝ n y := by
  simp [realDot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

def transverseProjectionMap (n : Position) : Vector →L[ℂ] Vector :=
  ContinuousLinearMap.id ℂ Vector - InnerProductSpace.rankOne ℂ (complexify n) (complexify n)

theorem transverseProjectionMap_apply (n : Position) (v : Vector) :
    transverseProjectionMap n v = transverseProjection n v := by
  simp only [transverseProjectionMap, sub_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.rankOne_apply, ← bilinear_complexify_eq_inner]
  rfl

def currentPlanePhase (k : ℝ) (n y : Position) : ℂ :=
  Complex.exp (-Complex.I * ((k * realDot n y : ℝ) : ℂ))

theorem currentPlanePhase_norm (k : ℝ) (n y : Position) : ‖currentPlanePhase k n y‖ = 1 := by
  simp [currentPlanePhase, Complex.norm_exp]

theorem compactCurrent_phase_integrable (k : ℝ) (p : CompactPolarization) (n : Position) :
    Integrable (fun y : Position => currentPlanePhase k n y • p.current y) volume := by
  have hm : Measurable (currentPlanePhase k n) := by unfold currentPlanePhase realDot; fun_prop
  apply (compactPolarization_current_integrable p).norm.mono' (hm.aestronglyMeasurable.smul p.memLp.aestronglyMeasurable)
  apply ae_of_all
  intro y
  change ‖currentPlanePhase k n y • p.current y‖ ≤ ‖p.current y‖
  rw [norm_smul, currentPlanePhase_norm, one_mul]

def compactCurrentFarField (k : ℝ) (p : CompactPolarization) (n : Position) : Vector :=
  ((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) • transverseProjection n
    (∫ y : Position, currentPlanePhase k n y • p.current y)

theorem compactCurrentFarField_integral (k : ℝ) (p : CompactPolarization) (n : Position) :
    compactCurrentFarField k p n = ∫ y : Position,
      (((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) * currentPlanePhase k n y) • transverseProjection n (p.current y) := by
  have hi := compactCurrent_phase_integrable k p n
  unfold compactCurrentFarField
  rw [← transverseProjectionMap_apply, ← (transverseProjectionMap n).integral_comp_comm hi,
    ← integral_smul]
  congr 1
  funext y
  rw [map_smul, transverseProjectionMap_apply, smul_smul]

theorem compactCurrentFarField_norm_le (k : ℝ) (p : CompactPolarization) (n : Position) (hn : ‖n‖ = 1) :
    ‖compactCurrentFarField k p n‖ ≤ (k ^ 2 / (4 * Real.pi)) * ∫ y : Position, ‖p.current y‖ := by
  rw [compactCurrentFarField, norm_smul,
    show ‖((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ)‖ = k ^ 2 / (4 * Real.pi) by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (transverseProjection_norm_le n hn _).trans
  calc
    _ ≤ ∫ y : Position, ‖currentPlanePhase k n y • p.current y‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul, currentPlanePhase_norm, one_mul]

theorem exteriorElectric_uniform_farField_error (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : 2 * p.radius + 2 ≤ ‖x‖) :
    ‖((‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))) • exteriorElectric k p x -
      compactCurrentFarField k p (radialDirection x)‖ ≤
      farFieldKernelConstant k p.radius / ‖x‖ * ∫ y : Position, ‖p.current y‖ := by
  have hi := exteriorElectric_integrable_far k p x (by linarith [p.radius_nonneg])
  have hp := (transverseProjectionMap (radialDirection x)).integrable_comp
    (compactCurrent_phase_integrable k p (radialDirection x))
  have hf : Integrable (fun y : Position => (((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) *
      currentPlanePhase k (radialDirection x) y) • transverseProjection (radialDirection x) (p.current y)) volume := by
    let T : Vector →L[ℂ] Vector := (((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ Vector
    simpa only [T, smul_apply, ContinuousLinearMap.id_apply, map_smul, transverseProjectionMap_apply, smul_smul, mul_comm] using
      T.integrable_comp hp
  have hsc : Integrable (fun y : Position =>
      ((‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))) •
        classicalDyadic k (x - y) (p.current y)) volume := by
    let T : Vector →L[ℂ] Vector :=
      ((‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))) • ContinuousLinearMap.id ℂ Vector
    simpa only [T, smul_apply, ContinuousLinearMap.id_apply] using T.integrable_comp hi
  rw [compactCurrentFarField_integral, exteriorElectric, ← integral_smul, ← integral_sub hsc hf]
  calc
    _ ≤ ∫ y : Position, (farFieldKernelConstant k p.radius / ‖x‖) * ‖p.current y‖ := by
      apply norm_integral_le_of_norm_le ((compactPolarization_current_integrable p).norm.const_mul _)
      apply ae_of_all
      intro y
      by_cases hy : ‖y‖ ≤ p.radius
      · simpa only [currentPlanePhase, realDot_eq_inner] using
          displaced_dyadic_farField_error k p.radius p.radius_nonneg x y hx hy (p.current y)
      · simp [p.vanish y (lt_of_not_ge hy), transverseProjection]
    _ = _ := integral_const_mul _ _

theorem compactCurrentFarField_continuous (k : ℝ) (p : CompactPolarization) :
    Continuous (compactCurrentFarField k p) := by
  have hc : Continuous (fun n : Position => ∫ y : Position, currentPlanePhase k n y • p.current y) := by
    apply continuous_of_dominated (bound := fun y : Position => ‖p.current y‖)
    · intro n
      exact (compactCurrent_phase_integrable k p n).aestronglyMeasurable
    · intro n
      exact ae_of_all _ (fun y => by simp [norm_smul, currentPlanePhase_norm])
    · exact (compactPolarization_current_integrable p).norm
    · apply ae_of_all
      intro y
      unfold currentPlanePhase realDot
      fun_prop
  unfold compactCurrentFarField transverseProjection complexify
  fun_prop

theorem volumePhysicalFarField_eq (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) (n : Position) :
    currentFarField k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) n =
      compactCurrentFarField k (bodyCurrentPolarization B f) n := by
  unfold currentFarField compactCurrentFarField
  congr 2
  rw [← integral_indicator (bodyDomain_isOpen B).measurableSet]
  apply integral_congr_ae
  filter_upwards [hp, bodyCurrentPolarization_current_ae B f, f.property] with x hx hf hsupport
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, ← hx]
    rfl
  · rw [indicator_of_notMem hxd, hf, hsupport hxd]
    simp

theorem outgoingElectric_uniform_physical_farField_error (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f))
    (x : Position) (hx : 2 * (bodyCurrentPolarization B f).radius + 2 ≤ ‖x‖) :
    ‖((‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))) •
        (volumeTotalElectric k σ (bodyCurrentPolarization B f) x - incidentElectric k σ x) -
      currentFarField k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) (radialDirection x)‖ ≤
      farFieldKernelConstant k (bodyCurrentPolarization B f).radius / ‖x‖ *
        ∫ y : Position, ‖(bodyCurrentPolarization B f).current y‖ := by
  rw [volumePhysicalFarField_eq k B σ f hp]
  have hext : x ∈ currentExterior (bodyCurrentPolarization B f) := by
    change (bodyCurrentPolarization B f).radius + 1 < ‖x‖
    linarith [(bodyCurrentPolarization B f).radius_nonneg]
  simp only [volumeTotalElectric, add_sub_cancel_left, outgoingElectricField, if_pos hext]
  exact exteriorElectric_uniform_farField_error k (bodyCurrentPolarization B f) x hx

end OQ7Prescribed
