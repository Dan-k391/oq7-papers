import PrescribedExtinction.OutgoingFundamental
import PrescribedExtinction.OutgoingVolumeIdentification
import PrescribedExtinction.DistributionVectorCalculus

/-! The actual compact-current scalar volume potential satisfies Helmholtz
in the original distribution space. Complex current correlations are
projected to genuine original real test functions before applying the proved
scalar fundamental solution. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

def polarizationCurrentComponentDistribution (p : CompactPolarization) (i : Fin 3) :
    ScalarDistribution := Distribution.ofFun ⊤ (fun x => p.current x i) volume ⊤

theorem polarizationCurrentComponentDistribution_apply (p : CompactPolarization)
    (i : Fin 3) (φ : ScalarTest) :
    polarizationCurrentComponentDistribution p i φ =
      ∫ x : Position, φ x • p.current x i := by
  apply Distribution.ofFun_apply
  exact (current_component_integrable p i).locallyIntegrable.locallyIntegrableOn ⊤

theorem polarizationCurrentComponentDistribution_eq_vectorL2 (p : CompactPolarization)
    (i : Fin 3) :
    polarizationCurrentComponentDistribution p i =
      vectorL2ComponentDistribution (p.memLp.toLp p.current) i := by
  ext φ
  rw [polarizationCurrentComponentDistribution_apply, vectorL2ComponentDistribution_apply]
  change (∫ x : Position, φ x • p.current x i) =
    (vectorCoordinate i) (∫ x : Position, φ x • (p.memLp.toLp p.current) x)
  rw [← (vectorCoordinate i).integral_comp_comm
    (φ.integrable_smul ((vectorL2_locallyIntegrable (p.memLp.toLp p.current)).locallyIntegrableOn ⊤))]
  apply integral_congr_ae
  filter_upwards [p.memLp.coeFn_toLp] with x hx
  rw [map_smul, hx]
  rfl

theorem currentCorrelation_zero_eq_current_test_integral (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    newtonCurrentCorrelation p φ i 0 = ∫ x : Position, φ x • p.current x i := by
  simp only [newtonCurrentCorrelation, zero_add, Complex.real_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm _ _

theorem potentialComponentDistribution_correlation_re_im (k : ℝ)
    (p : CompactPolarization) (φ : ScalarTest) (i : Fin 3) :
    potentialComponentDistribution k p i φ =
      outgoingGreenDistribution k (currentCorrelationRealTest Complex.reCLM p φ i) +
        Complex.I * outgoingGreenDistribution k
          (currentCorrelationRealTest Complex.imCLM p φ i) := by
  rw [potentialComponentDistribution_outgoing_pairing]
  rw [outgoingGreenDistribution_apply, outgoingGreenDistribution_apply]
  calc
    _ = ∫ z : Position, newtonCurrentCorrelation p φ i z * outgoingGreen k z := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => mul_comm _ _
    _ = _ := currentCorrelation_pairing_re_im p φ i (outgoingGreen_locallyIntegrable k)

theorem potentialComponent_helmholtz_apply (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) (φ : ScalarTest) :
    potentialComponentDistribution k p i (testLaplacian φ) +
      (k ^ 2) • potentialComponentDistribution k p i φ =
        -(∫ x : Position, φ x • p.current x i) := by
  have hr := outgoing_helmholtz_fundamental_apply k
    (currentCorrelationRealTest Complex.reCLM p φ i)
  have hi := outgoing_helmholtz_fundamental_apply k
    (currentCorrelationRealTest Complex.imCLM p φ i)
  simp only [testLaplacian_apply, Fin.sum_univ_three, map_add,
    currentCorrelationRealTest_partial, currentCorrelationRealTest_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul] at hr hi
  rw [← currentCorrelation_zero_eq_current_test_integral]
  rw [testLaplacian_apply]
  simp only [Fin.sum_univ_three, map_add,
    potentialComponentDistribution_correlation_re_im, Complex.real_smul]
  rw [← Complex.re_add_im (newtonCurrentCorrelation p φ i 0)]
  linear_combination hr + Complex.I * hi

/-- Exact Helmholtz equation for the existing actual scalar convolution
potential of every compactly supported vector L² current. -/
theorem potentialComponent_helmholtz_distribution (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) :
    distributionLaplacian (potentialComponentDistribution k p i) +
      (k ^ 2) • potentialComponentDistribution k p i =
        -polarizationCurrentComponentDistribution p i := by
  ext φ
  simp only [distributionLaplacian, Fin.sum_univ_three, add_apply, smul_apply,
    neg_apply, distributionPartial, Distribution.lineDerivCLM_apply, neg_neg,
    polarizationCurrentComponentDistribution_apply]
  have h := potentialComponent_helmholtz_apply k p i φ
  simpa [testLaplacian_apply, Fin.sum_univ_three, testPartial] using h

theorem potentialComponent_helmholtz_L2_distribution (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) :
    distributionLaplacian (potentialComponentDistribution k p i) +
      (k ^ 2) • potentialComponentDistribution k p i =
        -vectorL2ComponentDistribution (p.memLp.toLp p.current) i := by
  rw [← polarizationCurrentComponentDistribution_eq_vectorL2]
  exact potentialComponent_helmholtz_distribution k p i

end OQ7Prescribed
