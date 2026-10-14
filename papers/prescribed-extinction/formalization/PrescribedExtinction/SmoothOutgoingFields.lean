import PrescribedExtinction.IncidentMaxwell
import PrescribedExtinction.NewtonCurrentPairing
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
open scoped Convolution

def vectorScalarMulReal : Vector →L[ℝ] ℂ →L[ℝ] Vector :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Vector →L[ℝ] Vector).flip

theorem outgoingPotential_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    ContDiff ℝ (⊤ : ℕ∞) (outgoingPotential k p) := by
  exact (compactPolarization_current_hasCompactSupport p).contDiff_convolution_left
    vectorScalarMulReal hp (outgoingGreen_locallyIntegrable k)

theorem smoothField_partial_contDiff (F : Field) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ F x (basisR j)) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem smoothField_curl_contDiff (F : Field) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (curl F) := by
  have hj (j i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ F x (basisR j) i) :=
    (vectorCoordinate i).contDiff.comp (smoothField_partial_contDiff F hF j)
  unfold curl
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (hj 1 2).sub (hj 2 1)
  · exact (hj 2 0).sub (hj 0 2)
  · exact (hj 0 1).sub (hj 1 0)

theorem fieldComponentDistribution_injective (F G : Field)
    (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume)
    (h : fieldComponentDistribution F = fieldComponentDistribution G) : F =ᵐ[volume] G := by
  have hi (i : Fin 3) : (fun x => F x i) =ᵐ[volume] (fun x => G x i) := by
    simpa using Distribution.ofFun_injective
      ((fieldComponent_locallyIntegrable F hF i).locallyIntegrableOn ⊤)
      ((fieldComponent_locallyIntegrable G hG i).locallyIntegrableOn ⊤)
      (congrFun h i)
  filter_upwards [hi 0, hi 1, hi 2] with x h0 h1 h2
  ext i
  fin_cases i <;> assumption

theorem fieldComponentDistribution_sub (F G : Field)
    (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume) :
    fieldComponentDistribution (F - G) = fieldComponentDistribution F - fieldComponentDistribution G := by
  funext i
  have he : (fun x : Position => (F - G) x i) = (fun x => F x i) + -(fun x => G x i) := by
    funext x
    simp [sub_eq_add_neg]
  rw [fieldComponentDistribution, he, Distribution.ofFun_add
    ((fieldComponent_locallyIntegrable F hF i).locallyIntegrableOn ⊤)
    ((fieldComponent_locallyIntegrable G hG i).neg.locallyIntegrableOn ⊤),
    Distribution.ofFun_neg]
  rfl

theorem potentialComponent_eq_fieldComponent (k : ℝ) (p : CompactPolarization) :
    potentialComponentDistribution k p = fieldComponentDistribution (outgoingPotential k p) := by
  funext i
  ext φ
  rw [potentialComponentDistribution_apply,
    fieldComponentDistribution_apply _ (outgoingPotential_locallyIntegrable k p)]
  change (vectorCoordinate i) (∫ x : Position, φ x • outgoingPotential k p x) = _
  rw [← (vectorCoordinate i).integral_comp_comm
    (φ.integrable_smul ((outgoingPotential_locallyIntegrable k p).locallyIntegrableOn ⊤))]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [vectorCoordinate, Complex.real_smul]

/-- Smooth representatives of the exact contact-corrected physical source fields. -/
def smoothElectricSource (k : ℝ) (p : CompactPolarization) : Field :=
  curl (curl (outgoingPotential k p)) - p.current

def smoothMagneticSource (k : ℝ) (p : CompactPolarization) : Field :=
  fun x => (-Complex.I * (k : ℂ)) • curl (outgoingPotential k p) x

theorem smoothElectricSource_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothElectricSource k p) :=
  (smoothField_curl_contDiff _ (smoothField_curl_contDiff _ (outgoingPotential_contDiff k p hp))).sub hp

theorem smoothMagneticSource_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothMagneticSource k p) :=
  (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
    (fun _ : Position => (-Complex.I * (k : ℂ)))).smul
      (smoothField_curl_contDiff _ (outgoingPotential_contDiff k p hp))

theorem smoothElectricSource_distribution (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    fieldComponentDistribution (smoothElectricSource k p) = outgoingVolumeDistribution k p := by
  have hu := outgoingPotential_contDiff k p hp
  rw [smoothElectricSource, fieldComponentDistribution_sub _ _
    (smoothField_curl_contDiff _ (smoothField_curl_contDiff _ hu)).continuous.locallyIntegrable
    hp.continuous.locallyIntegrable, ← smoothField_distributionCurl _ (smoothField_curl_contDiff _ hu),
    ← smoothField_distributionCurl _ hu, ← potentialComponent_eq_fieldComponent]
  funext i
  rw [Pi.sub_apply, outgoingPotential_curlCurl]
  change outgoingVolumeDistribution k p i + polarizationCurrentComponentDistribution p i -
    polarizationCurrentComponentDistribution p i = _
  abel

theorem smoothMagneticSource_distribution (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    fieldComponentDistribution (smoothMagneticSource k p) = outgoingMagneticDistribution k p := by
  have hu := outgoingPotential_contDiff k p hp
  funext i
  change fieldComponentDistribution (fun x => (-Complex.I * (k : ℂ)) •
    curl (outgoingPotential k p) x) i = _
  rw [fieldComponentDistribution_complex_smul _ _
    (smoothField_curl_contDiff _ hu).continuous.locallyIntegrable i,
    ← smoothField_distributionCurl _ hu, ← potentialComponent_eq_fieldComponent]
  rfl

theorem smoothElectricSource_eq_ae (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    smoothElectricSource k p =ᵐ[volume] electricVolumeField k p := by
  apply fieldComponentDistribution_injective _ _
    (smoothElectricSource_contDiff k p hp).continuous.locallyIntegrable
    (locallySquareIntegrable_locallyIntegrable _ (electricVolumeField_locallySquareIntegrable k p))
  rw [smoothElectricSource_distribution k p hp]
  exact (funext (electricVolumeField_distribution k p)).symm

theorem smoothMagneticSource_eq_ae (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    smoothMagneticSource k p =ᵐ[volume] magneticVolumeField k p := by
  apply fieldComponentDistribution_injective _ _
    (smoothMagneticSource_contDiff k p hp).continuous.locallyIntegrable
    (locallySquareIntegrable_locallyIntegrable _ (magneticVolumeField_locallySquareIntegrable k p))
  rw [smoothMagneticSource_distribution k p hp]
  exact (funext (magneticVolumeField_distribution k p)).symm

theorem fieldComponentDistribution_smul (z : ℂ) (F : Field)
    (hF : LocallyIntegrable F volume) :
    fieldComponentDistribution (z • F) = z • fieldComponentDistribution F :=
  funext (fieldComponentDistribution_complex_smul z F hF)

theorem smoothElectricSource_curl (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    curl (smoothElectricSource k p) =
      fun x => (Complex.I * (k : ℂ)) • smoothMagneticSource k p x := by
  have he := smoothElectricSource_contDiff k p hp
  have hm := smoothMagneticSource_contDiff k p hp
  apply Measure.eq_of_ae_eq (μ := (volume : Measure Position)) _ (smoothField_curl_contDiff _ he).continuous
    ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Position => (Complex.I * (k : ℂ)))).smul hm).continuous
  apply fieldComponentDistribution_injective _ _
    (smoothField_curl_contDiff _ he).continuous.locallyIntegrable
    (hm.continuous.locallyIntegrable.smul (Complex.I * (k : ℂ)))
  rw [← smoothField_distributionCurl _ he, smoothElectricSource_distribution k p hp,
    outgoingVolumeDistribution_first_curl, fieldComponentDistribution_smul _ _ hm.continuous.locallyIntegrable,
    smoothMagneticSource_distribution k p hp]

theorem smoothMagneticSource_curl (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    curl (smoothMagneticSource k p) =
      fun x => (-Complex.I * (k : ℂ)) • (smoothElectricSource k p x + p.current x) := by
  have he := smoothElectricSource_contDiff k p hp
  have hm := smoothMagneticSource_contDiff k p hp
  have hsum := he.add hp
  apply Measure.eq_of_ae_eq (μ := (volume : Measure Position)) _ (smoothField_curl_contDiff _ hm).continuous
    ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Position => (-Complex.I * (k : ℂ)))).smul hsum).continuous
  apply fieldComponentDistribution_injective _ _
    (smoothField_curl_contDiff _ hm).continuous.locallyIntegrable
    (hsum.continuous.locallyIntegrable.smul (-Complex.I * (k : ℂ)))
  rw [← smoothField_distributionCurl _ hm, smoothMagneticSource_distribution k p hp,
    outgoingMagneticDistribution_second_curl]
  change (-Complex.I * (k : ℂ)) • (outgoingVolumeDistribution k p + polarizationCurrentComponentDistribution p) =
    fieldComponentDistribution ((-Complex.I * (k : ℂ)) • (smoothElectricSource k p + p.current))
  rw [fieldComponentDistribution_smul (-Complex.I * (k : ℂ))
    (smoothElectricSource k p + p.current) hsum.continuous.locallyIntegrable]
  have hadd := funext (fieldComponentDistribution_add (smoothElectricSource k p) p.current he.continuous.locallyIntegrable
    hp.continuous.locallyIntegrable)
  change fieldComponentDistribution (smoothElectricSource k p + p.current) =
    fieldComponentDistribution (smoothElectricSource k p) + fieldComponentDistribution p.current at hadd
  rw [hadd, smoothElectricSource_distribution k p hp]
  rfl

end OQ7Prescribed
