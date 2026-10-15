import PrescribedExtinction.UniversalFieldPowers
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def incidentForwardDirection (σ : Direction) : Position := σ.sign • basisR 2

theorem incidentForwardDirection_norm (σ : Direction) : ‖incidentForwardDirection σ‖ = 1 := by
  cases σ <;> simp [incidentForwardDirection, Direction.sign, basisR]

theorem forwardPlanePhase (k : ℝ) (σ : Direction) (x : Position) :
    currentPlanePhase k (incidentForwardDirection σ) x = star (planePhase k σ x) := by
  cases σ <;> simp [currentPlanePhase, realDot, incidentForwardDirection, Direction.sign,
    basisR, planePhase, Fin.sum_univ_succ, ← Complex.exp_conj, mul_comm]

theorem forwardProjection_component (σ : Direction) (v : Vector) :
    transverseProjection (incidentForwardDirection σ) v 1 = v 1 := by
  cases σ <;> simp [transverseProjection, incidentForwardDirection, Direction.sign, basisR, complexify]

theorem incidentPairing_phase_component (k : ℝ) (σ : Direction) (x : Position) (v : Vector) :
    pairing (incidentElectric k σ x) v = currentPlanePhase k (incidentForwardDirection σ) x * v 1 := by
  rw [forwardPlanePhase]
  simp [pairing, incidentElectric, basisC, Fin.sum_univ_succ]

theorem currentFarField_forward_component (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) (σ : Direction) :
    currentFarField k B E (incidentForwardDirection σ) 1 =
      ((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) *
        ∫ x in B.domain, pairing (incidentElectric k σ x) (polarization B E x) := by
  let p := physicalCompactPolarization B E hE
  have hi : Integrable (fun x : Position => currentPlanePhase k (incidentForwardDirection σ) x • polarization B E x)
      (volume.restrict B.domain) := (compactCurrent_phase_integrable k p (incidentForwardDirection σ)).restrict
  have hc := (vectorCoordinate 1).integral_comp_comm hi
  unfold currentFarField
  rw [PiLp.smul_apply, forwardProjection_component, smul_eq_mul]
  congr 1
  change vectorCoordinate 1 (∫ x in B.domain, currentPlanePhase k (incidentForwardDirection σ) x • polarization B E x) = _
  rw [← hc]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change vectorCoordinate 1 (currentPlanePhase k (incidentForwardDirection σ) x • polarization B E x) =
      pairing (incidentElectric k σ x) (polarization B E x)
    rw [incidentPairing_phase_component]
    rfl)

/-- The exact forward optical work identity for the original physical current
far field, for either original unit-amplitude incident plane wave. -/
theorem physical_forward_optical_theorem (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (E : Field) (hE : LocallySquareIntegrable E) (σ : Direction) :
    extinction k B σ E = (4 * Real.pi / k) *
      (pairing (basisC 1) (currentFarField k B E (incidentForwardDirection σ))).im := by
  have hb (v : Vector) : pairing (basisC 1) v = v 1 := by
    simp [pairing, basisC, Fin.sum_univ_succ]
  rw [hb, currentFarField_forward_component k B E hE σ]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, extinction]
  field_simp [hk.ne', Real.pi_ne_zero]

instance sphereArea_openPos : sphereArea.IsOpenPosMeasure := by
  unfold sphereArea
  infer_instance

theorem physicalScattering_zero_farField (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) (hS : scattering k B E = 0) :
    ∀ n : Position, ‖n‖ = 1 → currentFarField k B E n = 0 := by
  let F : UnitSphere → Vector := fun n => currentFarField k B E n
  have hF : Continuous F := (physicalCurrentFarField_continuous k B E hE).comp continuous_subtype_val
  have hi : Integrable (fun n : UnitSphere => ‖F n‖ ^ 2) sphereArea :=
    (hF.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : (fun n : UnitSphere => ‖F n‖ ^ 2) =ᵐ[sphereArea] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp
      (by rw [physicalScattering_eq_Haar k B E hE] at hS; exact hS)
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae (hF.norm.pow 2) continuous_const
  intro n hn
  let s : UnitSphere := ⟨n, by simpa [UnitSphere, Metric.mem_sphere, dist_zero_right] using hn⟩
  have hz := congrFun heq s
  change ‖currentFarField k B E n‖ ^ 2 = 0 at hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem physicalScattering_zero_extinction (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (E : Field) (hE : LocallySquareIntegrable E) (hS : scattering k B E = 0) (σ : Direction) :
    extinction k B σ E = 0 := by
  rw [physical_forward_optical_theorem k hk B E hE σ,
    physicalScattering_zero_farField k B E hE hS _ (incidentForwardDirection_norm σ)]
  simp [pairing]

theorem positiveExtinction_scattering_pos (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (E : Field) (hE : LocallySquareIntegrable E) (σ : Direction) (hX : 0 < extinction k B σ E) :
    0 < scattering k B E := by
  refine lt_of_le_of_ne (physicalScattering_nonneg k B E hE) ?_
  intro hz
  have h := physicalScattering_zero_extinction k hk B E hE hz.symm σ
  linarith

theorem scatteringState_forward_optical_theorem (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) : extinction k B σ s.electric =
      (4 * Real.pi / k) * (pairing (basisC 1)
        (currentFarField k B s.electric (incidentForwardDirection σ))).im :=
  physical_forward_optical_theorem k hk B _ s.maxwell.1 σ

theorem scatteringState_positiveExtinction_scattering_pos (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (σ : Direction) (s : ScatteringState k B σ)
    (hX : 0 < extinction k B σ s.electric) : 0 < scattering k B s.electric :=
  positiveExtinction_scattering_pos k hk B _ s.maxwell.1 σ hX

end OQ7Prescribed
