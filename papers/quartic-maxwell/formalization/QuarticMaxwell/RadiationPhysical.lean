import QuarticMaxwell.RadiationOperator
import QuarticMaxwell.MaskedRemainder
import PrescribedExtinction.FarFieldCurrent

/-! Exact correspondence between the newly bounded complete radiation map and
the existing genuine compact-current electric far-field amplitude. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem compactCurrentFarField_eq_radiationField (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) (n : UnitSphere) :
    compactCurrentFarField k (supportedPolarization R hR (supportInputCLM D hD hsub f)) n =
      (((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ)) • radiationField k D f n := by
  let p := supportedPolarization R hR (supportInputCLM D hD hsub f)
  have hcurrent : p.current =ᵐ[volume] D.indicator (fun y => f y) :=
    (supportedPolarization_current_ae R hR _).trans (supportInputCLM_coe D hD hsub f)
  unfold compactCurrentFarField
  congr 1
  rw [← transverseProjectionMap_apply,
    ← (transverseProjectionMap (n : Position)).integral_comp_comm
      (compactCurrent_phase_integrable k p n)]
  unfold radiationField
  rw [← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [hcurrent] with y hy
  rw [hy]
  by_cases hyd : y ∈ D <;>
    simp [hyd, angularProjection, transverseProjectionMap, currentPlanePhase,
      radiationPhase, realDot_eq_inner]

theorem compactCurrentFarField_power_eq (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    (∫ n : UnitSphere,
      ‖compactCurrentFarField k (supportedPolarization R hR (supportInputCLM D hD hsub f)) n‖ ^ 2 ∂sphereArea) =
      k ^ 4 / (16 * Real.pi ^ 2) * ‖radiationMap k D hD hfin f‖ ^ 2 := by
  have hcoef : ‖(((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ))‖ ^ 2 =
      k ^ 4 / (16 * Real.pi ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
    ring
  simp_rw [compactCurrentFarField_eq_radiationField k D hD hR hsub f,
    norm_smul, mul_pow, hcoef]
  rw [integral_const_mul, ← lp_integral_norm_sq sphereArea]
  congr 1
  apply integral_congr_ae
  filter_upwards [radiationLp_coe k D hfin f] with n hn
  exact congrArg (fun v : Vector => ‖v‖ ^ 2) hn.symm

end QuarticMaxwell
