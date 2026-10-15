import PrescribedExtinction.OutgoingDynamicIdentity
import PrescribedExtinction.RemainderCurrentPairing
import PrescribedExtinction.NewtonStaticIdentification

/-! Identification of the actual outgoing volume distribution on compact L²
currents. Complex current correlations are projected to genuine original
real test functions before the proved distributional Green identity is used. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

def currentCorrelationRealTest (L : ℂ →L[ℝ] ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) : ScalarTest where
  toFun z := L (newtonCurrentCorrelation p φ j z)
  contDiff' := L.contDiff.comp (newtonCurrentCorrelation_contDiff p φ j)
  hasCompactSupport' := (newtonCurrentCorrelation_hasCompactSupport p φ j).comp_left L.map_zero
  tsupport_subset' := subset_univ _

theorem currentCorrelationRealTest_apply (L : ℂ →L[ℝ] ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) (z : Position) :
    currentCorrelationRealTest L p φ j z = L (newtonCurrentCorrelation p φ j z) := rfl

theorem currentCorrelationRealTest_partial (L : ℂ →L[ℝ] ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (j i : Fin 3) :
    testPartial i (currentCorrelationRealTest L p φ j) =
      currentCorrelationRealTest L p (testPartial i φ) j := by
  ext z
  simp only [testPartial, TestFunction.lineDerivCLM_apply, top_add, le_top, ite_true]
  have h := newtonCurrentCorrelation_hasLineDerivAt p φ j i z
  change HasDerivAt (fun t : ℝ => newtonCurrentCorrelation p φ j (z + t • basisR i))
    (newtonCurrentCorrelation p (testPartial i φ) j z) 0 at h
  have hd := L.hasFDerivAt.comp_hasDerivAt 0 h
  change HasLineDerivAt ℝ (currentCorrelationRealTest L p φ j)
    (currentCorrelationRealTest L p (testPartial i φ) j z) z (basisR i) at hd
  exact hd.lineDeriv

theorem currentCorrelation_kernel_integrable (p : CompactPolarization) (φ : ScalarTest)
    (j : Fin 3) {f : Position → ℂ} (hf : LocallyIntegrable f volume) :
    Integrable (fun z => newtonCurrentCorrelation p φ j z * f z) volume := by
  exact hf.integrable_smul_left_of_hasCompactSupport
    (newtonCurrentCorrelation_contDiff p φ j).continuous
    (newtonCurrentCorrelation_hasCompactSupport p φ j)

theorem currentCorrelation_pairing_re_im (p : CompactPolarization) (φ : ScalarTest)
    (j : Fin 3) {f : Position → ℂ} (hf : LocallyIntegrable f volume) :
    (∫ z : Position, newtonCurrentCorrelation p φ j z * f z) =
      (∫ z : Position, currentCorrelationRealTest Complex.reCLM p φ j z • f z) +
        Complex.I * (∫ z : Position, currentCorrelationRealTest Complex.imCLM p φ j z • f z) := by
  have hr := (currentCorrelationRealTest Complex.reCLM p φ j).integrable_smul
    (hf.locallyIntegrableOn _)
  have hi := (currentCorrelationRealTest Complex.imCLM p φ j).integrable_smul
    (hf.locallyIntegrableOn _)
  rw [← integral_const_mul, ← integral_add hr (hi.const_mul Complex.I)]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [currentCorrelationRealTest_apply, Complex.reCLM_apply,
      Complex.imCLM_apply, Complex.real_smul]
    have h := Complex.re_add_im (newtonCurrentCorrelation p φ j z)
    calc
      _ = ((newtonCurrentCorrelation p φ j z).re +
          (newtonCurrentCorrelation p φ j z).im * Complex.I) * f z := by rw [h]
      _ = _ := by ring

theorem dynamicScalarRemainder_correlation_double_ibp (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (l i j : Fin 3) :
    (∫ z : Position, newtonCurrentCorrelation p (testPartial j (testPartial i φ)) l z *
      dynamicScalarRemainder k z) =
        ∫ z : Position, newtonCurrentCorrelation p φ l z * dynamicHessianRemainder k i j z := by
  rw [currentCorrelation_pairing_re_im p _ l (dynamicScalarRemainder_locallyIntegrable k),
    currentCorrelation_pairing_re_im p φ l (dynamicHessianRemainder_locallyIntegrable k i j)]
  rw [← currentCorrelationRealTest_partial, ← currentCorrelationRealTest_partial,
    ← currentCorrelationRealTest_partial, ← currentCorrelationRealTest_partial]
  rw [dynamicScalarRemainder_double_ibp, dynamicScalarRemainder_double_ibp]

theorem vector_basisC_expansion (v : Vector) : v = ∑ j : Fin 3, v j • basisC j := by
  ext i
  simp [basisC, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

theorem vector_clm_coordinate_expansion (A : Vector →L[ℂ] Vector) (v : Vector)
    (i : Fin 3) : A v i = ∑ j : Fin 3, v j * A (basisC j) i := by
  conv_lhs => rw [vector_basisC_expansion v]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]

theorem remainderPotentialComponentDistribution_pairing_sum (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    remainderPotentialComponentDistribution k p i φ =
      ∑ j : Fin 3, ∫ z : Position, newtonCurrentCorrelation p φ j z *
        dyadicRemainder k z (basisC j) i := by
  rw [remainderPotentialComponentDistribution_pairing]
  change (vectorCoordinate i) (∫ z : Position,
      dyadicRemainder k z (currentTestCorrelationVector p φ z)) = _
  rw [← (vectorCoordinate i).integral_comp_comm
    (remainder_current_correlation_pairing_integrable k p φ)]
  change (∫ z : Position, dyadicRemainder k z (currentTestCorrelationVector p φ z) i) = _
  calc
    _ = ∫ z : Position, ∑ j : Fin 3, newtonCurrentCorrelation p φ j z *
        dyadicRemainder k z (basisC j) i := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change dyadicRemainder k z (currentTestCorrelationVector p φ z) i =
          ∑ j : Fin 3, newtonCurrentCorrelation p φ j z * dyadicRemainder k z (basisC j) i
        rw [vector_clm_coordinate_expansion]
        simp only [currentTestCorrelationVector_coordinate]
    _ = _ := integral_finsetSum _ fun j _ => currentCorrelation_kernel_integrable p φ j
      (dyadicRemainderEntry_locallyIntegrable k i j)

theorem potentialComponentDistribution_dynamic_hessian_pairing (k : ℝ)
    (p : CompactPolarization) (φ : ScalarTest) (l i j : Fin 3) :
    potentialComponentDistribution k p l (testPartial j (testPartial i φ)) =
      potentialComponentDistribution 0 p l (testPartial j (testPartial i φ)) +
        ∫ z : Position, newtonCurrentCorrelation p φ l z * dynamicHessianRemainder k i j z := by
  rw [potentialComponentDistribution_outgoing_pairing,
    potentialComponentDistribution_outgoing_pairing,
    ← dynamicScalarRemainder_correlation_double_ibp]
  have hk := currentCorrelation_kernel_integrable p (testPartial j (testPartial i φ)) l
    (outgoingGreen_locallyIntegrable k)
  have h0 := currentCorrelation_kernel_integrable p (testPartial j (testPartial i φ)) l
    (outgoingGreen_locallyIntegrable 0)
  simp only [dynamicScalarRemainder, mul_sub]
  rw [integral_sub hk h0]
  simp only [mul_comm (outgoingGreen k _) _, mul_comm (outgoingGreen 0 _) _]
  abel

theorem dyadicRemainder_current_entry_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i j : Fin 3) :
    (∫ z : Position, newtonCurrentCorrelation p φ j z * dyadicRemainder k z (basisC j) i) =
      (∫ z : Position, newtonCurrentCorrelation p φ j z * dynamicHessianRemainder k i j z) +
        (if j = i then (k ^ 2) • potentialComponentDistribution k p i φ else 0) := by
  by_cases hij : j = i
  · subst j
    simp only [ite_true]
    rw [potentialComponentDistribution_outgoing_pairing, ← integral_smul]
    have hd := currentCorrelation_kernel_integrable p φ i
      (dynamicHessianRemainder_locallyIntegrable k i i)
    have hg := outgoing_current_correlation_pairing_integrable k p φ i
    have ha := integral_add hd (hg.smul (k ^ 2))
    change (∫ z : Position, newtonCurrentCorrelation p φ i z * dynamicHessianRemainder k i i z +
        (k ^ 2) • (outgoingGreen k z * newtonCurrentCorrelation p φ i z)) = _ at ha
    refine Eq.trans ?_ ha
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      simp only [dynamicHessianRemainder, ite_true, Complex.real_smul]
      ring
  · simp only [hij, ite_false, add_zero, dynamicHessianRemainder,
      Ne.symm hij, ite_false, sub_zero]

theorem remainderPotentialComponentDistribution_dynamic_pairing (k : ℝ)
    (p : CompactPolarization) (φ : ScalarTest) (i : Fin 3) :
    remainderPotentialComponentDistribution k p i φ =
      (k ^ 2) • potentialComponentDistribution k p i φ +
        ∑ j : Fin 3, ∫ z : Position, newtonCurrentCorrelation p φ j z *
          dynamicHessianRemainder k i j z := by
  rw [remainderPotentialComponentDistribution_pairing_sum]
  simp_rw [dyadicRemainder_current_entry_pairing]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact add_comm _ _

theorem outgoingVolumeDistribution_eq_zero_add_remainder (k : ℝ)
    (p : CompactPolarization) (i : Fin 3) :
    outgoingVolumeDistribution k p i = outgoingVolumeDistribution 0 p i +
      remainderPotentialComponentDistribution k p i := by
  ext φ
  have he (s : ℝ) : outgoingVolumeDistribution s p i φ =
      (s ^ 2) • potentialComponentDistribution s p i φ +
        ∑ j : Fin 3, potentialComponentDistribution s p j
          (testPartial j (testPartial i φ)) := by
    simp [outgoingVolumeDistribution, distributionPartial, testPartial,
      Distribution.lineDerivCLM_apply]
  rw [add_apply, he, he, remainderPotentialComponentDistribution_dynamic_pairing]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_smul, zero_add]
  have hs : (∑ j : Fin 3, potentialComponentDistribution k p j
      (testPartial j (testPartial i φ))) =
      (∑ j : Fin 3, potentialComponentDistribution 0 p j (testPartial j (testPartial i φ))) +
        ∑ j : Fin 3, ∫ z : Position, newtonCurrentCorrelation p φ j z *
          dynamicHessianRemainder k i j z := by
    calc
      _ = ∑ j : Fin 3, (potentialComponentDistribution 0 p j
          (testPartial j (testPartial i φ)) +
            ∫ z : Position, newtonCurrentCorrelation p φ j z * dynamicHessianRemainder k i j z) := by
        apply Finset.sum_congr rfl
        intro j _
        exact potentialComponentDistribution_dynamic_hessian_pairing k p φ j i j
      _ = _ := Finset.sum_add_distrib
  rw [hs]
  abel

/-- The actual outgoing dyadic volume distribution, including its static
contact term, is the bounded static Fourier operator plus the genuine
dynamic-minus-static convolution for every compactly supported L² current. -/
theorem outgoingVolumeDistribution_eq_staticFourier_add_remainder (k : ℝ)
    (p : CompactPolarization) (i : Fin 3) :
    outgoingVolumeDistribution k p i =
      vectorL2ComponentDistribution (staticFourierOperator (p.memLp.toLp p.current)) i +
        remainderPotentialComponentDistribution k p i := by
  rw [outgoingVolumeDistribution_eq_zero_add_remainder,
    outgoingVolumeDistribution_zero_eq_staticFourier]

end OQ7Prescribed
