import PrescribedExtinction.GradientCurrentPairing
import PrescribedExtinction.DyadicMaxwellSource

/-! Actual locally square-integrable electric and magnetic source fields.
Their original scalar distribution equations are proved from the physical
Green-current convolutions. Pointwise exterior representatives, radiation,
material solvability, and the vector-test weak-Maxwell bridge are separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

def electricVolumeField (k : ℝ) (p : CompactPolarization) : Field :=
  fun x => staticFourierOperator (p.memLp.toLp p.current) x + remainderPotential k p x

def potentialCurlField (k : ℝ) (p : CompactPolarization) : Field :=
  fun x =>
    (gradientPotential k p 1 x 2 - gradientPotential k p 2 x 1) • basisC 0 +
    (gradientPotential k p 2 x 0 - gradientPotential k p 0 x 2) • basisC 1 +
    (gradientPotential k p 0 x 1 - gradientPotential k p 1 x 0) • basisC 2

def magneticVolumeField (k : ℝ) (p : CompactPolarization) : Field :=
  fun x => (-Complex.I * (k : ℂ)) • potentialCurlField k p x

theorem electricVolumeField_locallySquareIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallySquareIntegrable (electricVolumeField k p) := by
  intro K hK
  exact ((Lp.memLp (staticFourierOperator (p.memLp.toLp p.current))).restrict K).add
    (remainderPotential_memLp_on_compact k p K hK)

theorem potentialCurlField_locallySquareIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallySquareIntegrable (potentialCurlField k p) := by
  intro K hK
  have h (j i : Fin 3) : MemLp (fun x => gradientPotential k p j x i) 2 (volume.restrict K) :=
    (gradientPotential_memLp_on_compact k p j K hK).continuousLinearMap_comp (vectorCoordinate i)
  have h0 := ((h 1 2).sub (h 2 1)).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℂ (basisC 0))
  have h1 := ((h 2 0).sub (h 0 2)).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℂ (basisC 1))
  have h2 := ((h 0 1).sub (h 1 0)).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℂ (basisC 2))
  exact (h0.add h1).add h2

theorem magneticVolumeField_locallySquareIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallySquareIntegrable (magneticVolumeField k p) := by
  intro K hK
  exact (potentialCurlField_locallySquareIntegrable k p K hK).const_smul (-Complex.I * (k : ℂ))

theorem locallySquareIntegrable_locallyIntegrable (F : Field)
    (hF : LocallySquareIntegrable F) : LocallyIntegrable F volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_one_iff_integrable.mp ((hF K hK).mono_exponent (by norm_num))

def fieldComponentDistribution (F : Field) (i : Fin 3) : ScalarDistribution :=
  Distribution.ofFun ⊤ (fun x => F x i) volume ⊤

theorem fieldComponentDistribution_apply (F : Field) (hF : LocallyIntegrable F volume)
    (i : Fin 3) (φ : ScalarTest) :
    fieldComponentDistribution F i φ = ∫ x : Position, (φ x : ℂ) * F x i := by
  have hl : LocallyIntegrable (fun x : Position => F x i) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact (vectorCoordinate i).integrable_comp (hF.integrableOn_isCompact hK)
  rw [fieldComponentDistribution, Distribution.ofFun_apply (hl.locallyIntegrableOn _)]
  simp only [Complex.real_smul]

theorem electricVolumeField_distribution (k : ℝ) (p : CompactPolarization) (i : Fin 3) :
    fieldComponentDistribution (electricVolumeField k p) i = outgoingVolumeDistribution k p i := by
  ext φ
  have hs := φ.integrable_smul
    ((vectorL2_locallyIntegrable (staticFourierOperator (p.memLp.toLp p.current))).locallyIntegrableOn ⊤)
  have hr := φ.integrable_smul ((remainderPotential_locallyIntegrable k p).locallyIntegrableOn ⊤)
  rw [fieldComponentDistribution_apply _
      (locallySquareIntegrable_locallyIntegrable _ (electricVolumeField_locallySquareIntegrable k p)),
    outgoingVolumeDistribution_eq_staticFourier_add_remainder, add_apply,
    vectorL2ComponentDistribution_apply, remainderPotentialComponentDistribution,
    Distribution.mapCLM_apply, remainderPotentialDistribution_apply]
  change (∫ x : Position, (φ x : ℂ) * electricVolumeField k p x i) =
    (vectorCoordinate i) (∫ x : Position, φ x • (staticFourierOperator (p.memLp.toLp p.current)) x) +
      (vectorCoordinate i) (∫ x : Position, φ x • remainderPotential k p x)
  rw [← (vectorCoordinate i).integral_comp_comm hs,
    ← (vectorCoordinate i).integral_comp_comm hr]
  have hi := integral_add ((vectorCoordinate i).integrable_comp hs)
    ((vectorCoordinate i).integrable_comp hr)
  refine Eq.trans ?_ hi
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp [electricVolumeField, vectorCoordinate, PiLp.add_apply, PiLp.smul_apply, Complex.real_smul, mul_add]

theorem magneticVolumeField_distribution (k : ℝ) (p : CompactPolarization) (i : Fin 3) :
    fieldComponentDistribution (magneticVolumeField k p) i = outgoingMagneticDistribution k p i := by
  ext φ
  have hm := locallySquareIntegrable_locallyIntegrable _ (magneticVolumeField_locallySquareIntegrable k p)
  have hi (j l : Fin 3) : Integrable (fun x : Position => (φ x : ℂ) * gradientPotential k p j x l) volume := by
    have hv := φ.integrable_smul ((gradientPotential_locallyIntegrable k p j).locallyIntegrableOn ⊤)
    exact (vectorCoordinate l).integrable_comp hv
  rw [fieldComponentDistribution_apply _ hm]
  fin_cases i
  all_goals
    simp [outgoingMagneticDistribution, distributionCurl, potentialComponent_first_distribution,
      gradientPotentialComponentDistribution_apply, magneticVolumeField, potentialCurlField,
      PiLp.smul_apply, PiLp.add_apply, basisC]
    rw [integral_neg]
    congr 1
    rw [← integral_sub (hi _ _) (hi _ _), ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring

/-- The physical electric and magnetic fields satisfy the first source curl
equation in the original continuous scalar distributions. -/
theorem physicalSourceFields_first_curl (k : ℝ) (p : CompactPolarization) :
    distributionCurl (fieldComponentDistribution (electricVolumeField k p)) =
      (Complex.I * (k : ℂ)) • fieldComponentDistribution (magneticVolumeField k p) := by
  have he := funext (electricVolumeField_distribution k p)
  have hm := funext (magneticVolumeField_distribution k p)
  rw [he, hm]
  exact outgoingVolumeDistribution_first_curl k p

/-- The physical source fields satisfy the second source curl equation.
The compact polarization is the original L² current, not an assumed material
response or optical identity. -/
theorem physicalSourceFields_second_curl (k : ℝ) (p : CompactPolarization) :
    distributionCurl (fieldComponentDistribution (magneticVolumeField k p)) =
      (-Complex.I * (k : ℂ)) •
        (fieldComponentDistribution (electricVolumeField k p) + polarizationCurrentComponentDistribution p) := by
  rw [funext (electricVolumeField_distribution k p), funext (magneticVolumeField_distribution k p)]
  exact outgoingMagneticDistribution_second_curl k p

end OQ7Prescribed
