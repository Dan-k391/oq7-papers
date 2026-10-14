import PrescribedExtinction.WeakCurlBridge
import PrescribedExtinction.ExteriorOutgoing

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem newtonHessian_test_integrable_of_zero (φ : ScalarTest) (hφ : φ 0 = 0) (i j : Fin 3) :
    Integrable (fun x : Position => newtonHessianKernel i j x * φ x) volume := by
  apply (newtonCompensated_integrable φ i j).congr
  exact ae_of_all _ fun x => by simp [newtonCompensated, hφ]

theorem newtonPVValue_eq_integral_of_zero (φ : ScalarTest) (hφ : φ 0 = 0) (i j : Fin 3) :
    newtonPVValue φ i j = ∫ x : Position, newtonHessianKernel i j x * φ x := by
  simp [newtonPVValue, newtonCompensated, hφ]

theorem classicalDyadic_zero_coordinate (x : Position) (i j : Fin 3) :
    classicalDyadic 0 x (basisC j) i = (newtonHessianKernel i j x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [classicalDyadic, outgoingRadial, outgoingRadialFirst, outgoingRadialSecond,
      newtonHessianKernel]
  rw [classicalDyadic_coordinate 0 x hx, ← newtonHessianKernel_classical i j x hx]
  simp

/-- The actual dyadic kernel acts by an absolutely convergent integral when
the test vanishes at the pole. The full contact identity remains in force;
its Dirac term vanishes here because the test value is proved zero. -/
theorem dyadicGreenDistribution_apply_of_zero (k : ℝ) (φ : ScalarTest)
    (hφ : φ 0 = 0) (i j : Fin 3) :
    dyadicGreenDistribution k i j φ =
      ∫ x : Position, (φ x : ℂ) * classicalDyadic k x (basisC j) i := by
  have hn : Integrable (fun x : Position => ((newtonHessianKernel i j x * φ x : ℝ) : ℂ)) volume :=
    (newtonHessian_test_integrable_of_zero φ hφ i j).ofReal
  have hr : Integrable (fun x : Position => (φ x : ℂ) * dyadicRemainder k x (basisC j) i) volume := by
    simpa only [Complex.real_smul] using
      φ.integrable_smul ((dyadicRemainderEntry_locallyIntegrable k i j).locallyIntegrableOn _)
  rw [dyadicGreenDistribution_eq_static_add_remainder, add_apply,
    newton_hessian_contact_apply, hφ, mul_zero, sub_zero,
    newtonPVValue_eq_integral_of_zero φ hφ,
    Distribution.ofFun_apply ((dyadicRemainderEntry_locallyIntegrable k i j).locallyIntegrableOn _)]
  simp only [Complex.real_smul]
  rw [← integral_complex_ofReal, ← integral_add hn hr]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [Complex.ofReal_mul, dyadicRemainder, sub_apply, PiLp.sub_apply, Pi.add_apply,
      classicalDyadic_zero_coordinate]
    ring

theorem classicalDyadic_test_integrable_of_zero (k : ℝ) (φ : ScalarTest)
    (hφ : φ 0 = 0) (i j : Fin 3) :
    Integrable (fun x : Position => (φ x : ℂ) * classicalDyadic k x (basisC j) i) volume := by
  have hn : Integrable (fun x : Position => ((newtonHessianKernel i j x * φ x : ℝ) : ℂ)) volume :=
    (newtonHessian_test_integrable_of_zero φ hφ i j).ofReal
  have hr : Integrable (fun x : Position => (φ x : ℂ) * dyadicRemainder k x (basisC j) i) volume := by
    simpa only [Complex.real_smul] using
      φ.integrable_smul ((dyadicRemainderEntry_locallyIntegrable k i j).locallyIntegrableOn _)
  apply (hn.add hr).congr
  exact ae_of_all _ fun x => by
    simp only [Complex.ofReal_mul, dyadicRemainder, sub_apply, PiLp.sub_apply, Pi.add_apply,
      classicalDyadic_zero_coordinate]
    ring

theorem currentCorrelation_zero_of_exterior_test (p : CompactPolarization) (φ : ScalarTest)
    (hφ : ∀ x : Position, ‖x‖ ≤ p.radius → φ x = 0) (i : Fin 3) :
    newtonCurrentCorrelation p φ i 0 = 0 := by
  unfold newtonCurrentCorrelation
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro y
  by_cases hy : ‖y‖ ≤ p.radius
  · simp [hφ y hy]
  · simp [p.vanish y (lt_of_not_ge hy)]

def currentDyadicTestPairing (k : ℝ) (p : CompactPolarization) (φ : ScalarTest) (i j : Fin 3) : ℂ :=
  dyadicGreenDistribution k i j (currentCorrelationRealTest Complex.reCLM p φ j) +
    Complex.I * dyadicGreenDistribution k i j (currentCorrelationRealTest Complex.imCLM p φ j)

theorem currentCorrelation_green_distribution_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) :
    outgoingGreenDistribution k (currentCorrelationRealTest Complex.reCLM p φ j) +
      Complex.I * outgoingGreenDistribution k (currentCorrelationRealTest Complex.imCLM p φ j) =
        potentialComponentDistribution k p j φ := by
  rw [outgoingGreenDistribution_apply, outgoingGreenDistribution_apply,
    potentialComponentDistribution_outgoing_pairing]
  simpa only [mul_comm] using currentCorrelation_pairing_re_im p φ j (outgoingGreen_locallyIntegrable k) |>.symm

theorem currentCorrelation_greenHessian_distribution_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i j : Fin 3) :
    greenHessian k i j (currentCorrelationRealTest Complex.reCLM p φ j) +
      Complex.I * greenHessian k i j (currentCorrelationRealTest Complex.imCLM p φ j) =
        potentialComponentDistribution k p j (testPartial j (testPartial i φ)) := by
  rw [greenHessian_apply, greenHessian_apply]
  rw [currentCorrelationRealTest_partial, currentCorrelationRealTest_partial,
    currentCorrelationRealTest_partial, currentCorrelationRealTest_partial]
  exact currentCorrelation_green_distribution_pairing k p _ j

theorem currentDyadicTestPairing_eq (k : ℝ) (p : CompactPolarization) (φ : ScalarTest) (i j : Fin 3) :
    currentDyadicTestPairing k p φ i j =
      (if i = j then (k ^ 2) • potentialComponentDistribution k p j φ else 0) +
        potentialComponentDistribution k p j (testPartial j (testPartial i φ)) := by
  have hg := currentCorrelation_green_distribution_pairing k p φ j
  have hh := currentCorrelation_greenHessian_distribution_pairing k p φ i j
  unfold currentDyadicTestPairing dyadicGreenDistribution
  by_cases hij : i = j
  · simp only [hij, ite_true, add_apply, smul_apply, Complex.real_smul]
    have he := congrArg (fun z : ℂ => ((k ^ 2 : ℝ) : ℂ) * z) hg
    simp only [hij] at hg hh he
    linear_combination he + hh
  · simp only [hij, ite_false, zero_apply, zero_add, add_apply]
    exact hh

theorem outgoingVolumeDistribution_current_dyadic_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    outgoingVolumeDistribution k p i φ = ∑ j : Fin 3, currentDyadicTestPairing k p φ i j := by
  have he : outgoingVolumeDistribution k p i φ =
      (k ^ 2) • potentialComponentDistribution k p i φ +
        ∑ j : Fin 3, potentialComponentDistribution k p j (testPartial j (testPartial i φ)) := by
    simp [outgoingVolumeDistribution, distributionPartial, testPartial, Distribution.lineDerivCLM_apply]
  rw [he]
  simp_rw [currentDyadicTestPairing_eq]
  rw [Finset.sum_add_distrib]
  simp

theorem currentDyadicTestPairing_exterior_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius → φ x = 0) (i j : Fin 3) :
    Integrable (fun z : Position => newtonCurrentCorrelation p φ j z *
      classicalDyadic k z (basisC j) i) volume := by
  have hz := currentCorrelation_zero_of_exterior_test p φ hφ j
  have ht (L : ℂ →L[ℝ] ℝ) : currentCorrelationRealTest L p φ j 0 = 0 := by
    simp [currentCorrelationRealTest_apply, hz]
  have hr := classicalDyadic_test_integrable_of_zero k _ (ht Complex.reCLM) i j
  have hi := classicalDyadic_test_integrable_of_zero k _ (ht Complex.imCLM) i j
  apply (hr.add (hi.const_mul Complex.I)).congr
  exact ae_of_all _ fun z => by
    simp only [Pi.add_apply, currentCorrelationRealTest_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    have h := Complex.re_add_im (newtonCurrentCorrelation p φ j z)
    calc
      _ = ((newtonCurrentCorrelation p φ j z).re +
        (newtonCurrentCorrelation p φ j z).im * Complex.I) * classicalDyadic k z (basisC j) i := by ring
      _ = _ := by rw [h]

theorem currentDyadicTestPairing_exterior_integral (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius → φ x = 0) (i j : Fin 3) :
    currentDyadicTestPairing k p φ i j = ∫ z : Position, newtonCurrentCorrelation p φ j z *
      classicalDyadic k z (basisC j) i := by
  have hz := currentCorrelation_zero_of_exterior_test p φ hφ j
  have ht (L : ℂ →L[ℝ] ℝ) : currentCorrelationRealTest L p φ j 0 = 0 := by
    simp [currentCorrelationRealTest_apply, hz]
  have hr := classicalDyadic_test_integrable_of_zero k _ (ht Complex.reCLM) i j
  have hi := classicalDyadic_test_integrable_of_zero k _ (ht Complex.imCLM) i j
  rw [currentDyadicTestPairing, dyadicGreenDistribution_apply_of_zero k _ (ht Complex.reCLM),
    dyadicGreenDistribution_apply_of_zero k _ (ht Complex.imCLM), ← integral_const_mul,
    ← integral_add hr (hi.const_mul Complex.I)]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [currentCorrelationRealTest_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    calc
      _ = ((newtonCurrentCorrelation p φ j z).re +
        (newtonCurrentCorrelation p φ j z).im * Complex.I) * classicalDyadic k z (basisC j) i := by ring
      _ = _ := by rw [Complex.re_add_im]

end OQ7Prescribed
