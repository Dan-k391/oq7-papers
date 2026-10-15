import PrescribedExtinction.PhysicalOpticalBalance
import PrescribedExtinction.TensorLossCoercivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem bodyPermittivity_admissible_on_domain (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (x : Position) (hx : x ∈ B.domain) :
    MaterialAdmissible P Q (B.permittivity x) := by
  simp only [TwoLayerBody.permittivity, hx, ite_true]
  split_ifs
  · exact hB.1
  · exact hB.2

theorem material_quadratic_im_nonneg (P Q : ℝ) (T : Tensor)
    (hT : MaterialAdmissible P Q T) (v : Vector) : 0 ≤ (quadratic T v).im := by
  by_cases hv : v = 0
  · simp [hv, quadratic, pairing, tensorApply]
  · exact (hT.2.2.1 v hv).le

theorem physicalAbsorption_nonneg (k : ℝ) (hk : 0 ≤ k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (E : Field) : 0 ≤ absorption k B E := by
  apply mul_nonneg hk
  apply setIntegral_nonneg (bodyDomain_isOpen B).measurableSet
  intro x hx
  exact material_quadratic_im_nonneg P Q _ (bodyPermittivity_admissible_on_domain P Q B hB x hx) _

theorem physicalAbsorption_integrable (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) :
    IntegrableOn (fun x => (quadratic (B.permittivity x) (E x)).im) B.domain volume := by
  let e := bodyFieldCurrent B E hE
  let hp := physicalPolarization_memLp B E hE
  let p := hp.toLp (polarization B E)
  have hi := (L2.integrable_inner (𝕜 := ℂ) (e : VectorL2) p).im
  have heq : (fun x => (inner ℂ ((e : VectorL2) x) (p x)).im) =ᵐ[volume]
      B.domain.indicator (fun x => (quadratic (B.permittivity x) (E x)).im) := by
    filter_upwards [bodyFieldCurrent_coe B E hE, hp.coeFn_toLp] with x he hp
    rw [he, hp]
    by_cases hx : x ∈ B.domain
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      exact susceptibility_quadratic_im (B.permittivity x) (E x)
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_left]
      rfl
  exact (integrable_indicator_iff (bodyDomain_isOpen B).measurableSet).mp (hi.congr heq)

theorem physicalCurrentFarField_eq_compact (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) (n : Position) :
    currentFarField k B E n = compactCurrentFarField k (physicalCompactPolarization B E hE) n := by
  unfold currentFarField compactCurrentFarField
  congr 2
  rw [← integral_indicator (bodyDomain_isOpen B).measurableSet]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases hx : x ∈ B.domain
  · rw [indicator_of_mem hx]
    rfl
  · rw [indicator_of_notMem hx]
    have hz : polarization B E x = 0 := by
      rw [physicalPolarization_indicator, indicator_of_notMem hx]
    simp only [physicalCompactPolarization, hz, smul_zero]

theorem physicalCurrentFarField_continuous (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) : Continuous (currentFarField k B E) := by
  have he := funext (physicalCurrentFarField_eq_compact k B E hE)
  rw [he]
  exact compactCurrentFarField_continuous k _

theorem physicalScattering_eq_Haar (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) : scattering k B E =
      ∫ n : UnitSphere, ‖currentFarField k B E n‖ ^ 2 ∂sphereArea := by
  unfold scattering
  simp_rw [squareNorm_eq_norm_sq]
  exact (sphereArea_integral_original_angles (fun n => ‖currentFarField k B E n‖ ^ 2)
    ((physicalCurrentFarField_continuous k B E hE).norm.pow 2)).symm

theorem physicalScattering_nonneg (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) : 0 ≤ scattering k B E := by
  rw [physicalScattering_eq_Haar k B E hE]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem physicalAsymmetry_nonneg (k : ℝ) (B : TwoLayerBody) (Ep Em : Field)
    (hX : 0 ≤ extinction k B .plus Ep) : 0 ≤ normalizedAsymmetry k B Ep Em :=
  div_nonneg (abs_nonneg _) hX

theorem scatteringState_absorption_nonneg (k : ℝ) (hk : 0 ≤ k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (σ : Direction) (s : ScatteringState k B σ) :
    0 ≤ absorption k B s.electric := physicalAbsorption_nonneg k hk P Q B hB _

theorem scatteringState_absorption_integrable (k : ℝ) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) :
    IntegrableOn (fun x => (quadratic (B.permittivity x) (s.electric x)).im) B.domain volume :=
  physicalAbsorption_integrable B _ s.maxwell.1

theorem scatteringState_scattering_nonneg (k : ℝ) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) : 0 ≤ scattering k B s.electric :=
  physicalScattering_nonneg k B _ s.maxwell.1

end OQ7Prescribed
