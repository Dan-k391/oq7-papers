import PrescribedExtinction.VolumeFundamental
import PrescribedExtinction.CompactOutgoingIdentification

/-! Maxwell source equations for the actual outgoing Green volume potential.
The compact current is arbitrary; the Helmholtz identity and all derivative
commutations are proved dependencies. No material equation or radiation
condition is assumed. These distribution equations do not yet assert existence
of locally square-integrable magnetic fields or of scattering states. -/
noncomputable section
namespace OQ7Prescribed

theorem distributionCurl_add (U V : CartesianDistribution) :
    distributionCurl (U + V) = distributionCurl U + distributionCurl V := by
  funext i
  fin_cases i <;> simp [distributionCurl, map_add] <;> abel

theorem distributionCurl_real_smul (a : ℝ) (U : CartesianDistribution) :
    distributionCurl (a • U) = a • distributionCurl U := by
  funext i
  fin_cases i <;> simp [distributionCurl, map_smul, smul_sub]

theorem distributionPartial_complex_smul (a : ℂ) (T : ScalarDistribution) (i : Fin 3) :
    distributionPartial i (a • T) = a • distributionPartial i T := by
  ext φ
  simp [distributionPartial, Distribution.lineDerivCLM_apply, smul_neg]

theorem distributionCurl_complex_smul (a : ℂ) (U : CartesianDistribution) :
    distributionCurl (a • U) = a • distributionCurl U := by
  funext i
  fin_cases i <;> simp [distributionCurl, distributionPartial_complex_smul, smul_sub]

theorem outgoingVolumeDistribution_eq_gradient (k : ℝ) (p : CompactPolarization) :
    outgoingVolumeDistribution k p =
      (k ^ 2) • potentialComponentDistribution k p +
        (fun i => distributionPartial i
          (distributionDivergence (potentialComponentDistribution k p))) := by
  funext i
  simp only [outgoingVolumeDistribution, distributionDivergence, map_sum,
    Pi.add_apply, Pi.smul_apply]

theorem outgoingVolumeDistribution_curl (k : ℝ) (p : CompactPolarization) :
    distributionCurl (outgoingVolumeDistribution k p) =
      (k ^ 2) • distributionCurl (potentialComponentDistribution k p) := by
  rw [outgoingVolumeDistribution_eq_gradient, distributionCurl_add,
    distributionCurl_real_smul, distributionCurl_gradient, add_zero]

theorem outgoingPotential_curlCurl (k : ℝ) (p : CompactPolarization) (i : Fin 3) :
    distributionCurl (distributionCurl (potentialComponentDistribution k p)) i =
      outgoingVolumeDistribution k p i + polarizationCurrentComponentDistribution p i := by
  rw [distributionCurlCurl]
  have h := eq_sub_of_add_eq (potentialComponent_helmholtz_distribution k p i)
  rw [h, outgoingVolumeDistribution, distributionDivergence, map_sum]
  abel

/-- The physical dyadic Green potential solves the exact Maxwell second-order
source equation, including the distributional contact contribution. -/
theorem outgoingVolumeDistribution_maxwell_source (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) :
    distributionCurl (distributionCurl (outgoingVolumeDistribution k p)) i -
      (k ^ 2) • outgoingVolumeDistribution k p i =
        (k ^ 2) • polarizationCurrentComponentDistribution p i := by
  rw [outgoingVolumeDistribution_curl, distributionCurl_real_smul]
  simp only [Pi.smul_apply, outgoingPotential_curlCurl, smul_add]
  abel

/-- The same identity on the original vector L² current, with no smoothness
restriction on the current. -/
theorem outgoingVolumeDistribution_maxwell_source_L2 (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) :
    distributionCurl (distributionCurl (outgoingVolumeDistribution k p)) i -
      (k ^ 2) • outgoingVolumeDistribution k p i =
        (k ^ 2) • vectorL2ComponentDistribution (p.memLp.toLp p.current) i := by
  rw [← polarizationCurrentComponentDistribution_eq_vectorL2]
  exact outgoingVolumeDistribution_maxwell_source k p i

/-- Impedance-normalized magnetic distribution of the actual Green potential.
Its locally square-integrable field realization and pointwise exterior
representative remain separate analytic obligations. -/
def outgoingMagneticDistribution (k : ℝ) (p : CompactPolarization) :
    CartesianDistribution :=
  (-Complex.I * (k : ℂ)) • distributionCurl (potentialComponentDistribution k p)

/-- First exact curl equation for the actual electric dyadic distribution. -/
theorem outgoingVolumeDistribution_first_curl (k : ℝ) (p : CompactPolarization) :
    distributionCurl (outgoingVolumeDistribution k p) =
      (Complex.I * (k : ℂ)) • outgoingMagneticDistribution k p := by
  rw [outgoingVolumeDistribution_curl, outgoingMagneticDistribution, smul_smul]
  have hc : (Complex.I * (k : ℂ)) * (-Complex.I * (k : ℂ)) = ((k ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_pow]
    calc
      _ = -(Complex.I * Complex.I) * (k : ℂ) ^ 2 := by ring
      _ = (k : ℂ) ^ 2 := by simp [Complex.I_mul_I]
  rw [hc]
  funext i
  ext φ
  simp [Complex.real_smul]

/-- Second exact curl equation, with the original compact polarization source. -/
theorem outgoingMagneticDistribution_second_curl (k : ℝ) (p : CompactPolarization) :
    distributionCurl (outgoingMagneticDistribution k p) =
      (-Complex.I * (k : ℂ)) •
        (outgoingVolumeDistribution k p + polarizationCurrentComponentDistribution p) := by
  rw [outgoingMagneticDistribution, distributionCurl_complex_smul]
  congr 1
  funext i
  exact outgoingPotential_curlCurl k p i

end OQ7Prescribed
