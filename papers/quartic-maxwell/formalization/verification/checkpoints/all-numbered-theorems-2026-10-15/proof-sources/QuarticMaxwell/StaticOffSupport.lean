import QuarticMaxwell.SphereStatic
import QuarticMaxwell.StaticHessian
import PrescribedExtinction.OutgoingVolumeIdentification

/-! The actual Newton Hessian kernel on separated source and test supports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed SphereStatic MeasureTheory Set

theorem test_zero_of_norm_le (φ : ScalarTest) {r : ℝ}
    (hs : tsupport (φ : OQ7Prescribed.Position → ℝ) ⊆ {x | r < ‖x‖}) (x : OQ7Prescribed.Position) (hx : ‖x‖ ≤ r) :
    φ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_lt_of_ge hx) (hs hmem)

theorem newton_double_ibp_away (φ : ScalarTest) {r : ℝ} (hr : 0 < r)
    (hs : tsupport (φ : OQ7Prescribed.Position → ℝ) ⊆ {x | r < ‖x‖}) (i j : Fin 3) :
    (∫ x : OQ7Prescribed.Position, newtonReal x * (testPartial j (testPartial i φ)) x) =
      ∫ x : OQ7Prescribed.Position, newtonHessianKernel i j x * φ x := by
  have h1 := testPartial_tsupport i φ
  have h2 := testPartial_tsupport j (testPartial i φ)
  have hz (x : OQ7Prescribed.Position) (hx : ‖x‖ ≤ r) : φ x = 0 := test_zero_of_norm_le φ hs x hx
  have hd (x : OQ7Prescribed.Position) (hx : ‖x‖ ≤ r) : testPartial i φ x = 0 :=
    test_zero_of_norm_le _ (h1.trans hs) x hx
  have hdd (x : OQ7Prescribed.Position) (hx : ‖x‖ ≤ r) : testPartial j (testPartial i φ) x = 0 :=
    test_zero_of_norm_le _ (h2.trans (h1.trans hs)) x hx
  have hb (n : UnitSphere) : ‖r • (n : OQ7Prescribed.Position)‖ ≤ r := by
    simp [norm_smul, abs_of_pos hr]
  have hc : newtonContactBoundary φ i j r = 0 := by
    simp [newtonContactBoundary, hz _ (hb _)]
  have hbd : newtonDerivativeBoundary φ i j r = 0 := by
    simp [newtonDerivativeBoundary, hd _ (hb _)]
  have h := newton_punctured_double_ibp r hr φ i j
  rw [hc, hbd, add_zero, add_zero] at h
  unfold newtonPVTruncated at h
  have he (F : OQ7Prescribed.Position → ℝ) (hF : ∀ x, ‖x‖ ≤ r → F x = 0) :
      (∫ x in {x : OQ7Prescribed.Position | r < ‖x‖}, F x) = ∫ x, F x := by
    rw [← integral_indicator (isOpen_lt continuous_const continuous_norm).measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      by_cases hx : r < ‖x‖
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx, hF x (le_of_not_gt hx)])
  rw [he _ (fun x hx => by rw [hdd x hx, mul_zero]),
    he _ (fun x hx => by rw [hz x hx, mul_zero])] at h
  exact h

end QuarticMaxwell.StaticOffSupport

namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed SphereStatic MeasureTheory Set

def exteriorHessianEntry (r : ℝ) (i j : Fin 3) : OQ7Prescribed.Position → ℂ :=
  {x : OQ7Prescribed.Position | r < ‖x‖}.indicator (fun x => (newtonHessianKernel i j x : ℂ))

theorem exteriorHessianEntry_measurable (r : ℝ) (i j : Fin 3) :
    Measurable (exteriorHessianEntry r i j) :=
  (Complex.measurable_ofReal.comp (newtonHessianKernel_measurable i j)).indicator
    (isOpen_lt continuous_const continuous_norm).measurableSet

theorem exteriorHessianEntry_bound {r : ℝ} (hr : 0 < r) (i j : Fin 3) (x : OQ7Prescribed.Position) :
    ‖exteriorHessianEntry r i j x‖ ≤ Real.pi⁻¹ * r⁻¹ ^ 3 := by
  by_cases hx : r < ‖x‖
  · simp only [exteriorHessianEntry, Set.indicator, Set.mem_ofPred_eq, hx, ite_true, Complex.norm_real]
    apply (newtonHessianKernel_norm_le i j x).trans
    gcongr
  · simp only [exteriorHessianEntry, Set.indicator, Set.mem_ofPred_eq, hx, ite_false, norm_zero]
    positivity

theorem exteriorHessianEntry_locallyIntegrable {r : ℝ} (hr : 0 < r) (i j : Fin 3) :
    LocallyIntegrable (exteriorHessianEntry r i j) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (exteriorHessianEntry_measurable r i j).aestronglyMeasurable
    (ae_of_all _ (exteriorHessianEntry_bound hr i j))

theorem scalarNewton_double_ibp_away (φ : ScalarTest) {r : ℝ} (hr : 0 < r)
    (hs : tsupport (φ : OQ7Prescribed.Position → ℝ) ⊆ {x | r < ‖x‖}) (i j : Fin 3) :
    (∫ x : OQ7Prescribed.Position, (testPartial j (testPartial i φ)) x • outgoingGreen 0 x) =
      ∫ x : OQ7Prescribed.Position, φ x • exteriorHessianEntry r i j x := by
  have hL : (fun x : OQ7Prescribed.Position => (testPartial j (testPartial i φ)) x • outgoingGreen 0 x) =
      (fun x => ((newtonReal x * (testPartial j (testPartial i φ)) x : ℝ) : ℂ)) := by
    funext x
    rw [← newtonReal_eq_green]
    simp [Complex.real_smul, mul_comm]
  have hR : (fun x : OQ7Prescribed.Position => φ x • exteriorHessianEntry r i j x) =
      (fun x => ((newtonHessianKernel i j x * φ x : ℝ) : ℂ)) := by
    funext x
    by_cases hx : x ∈ tsupport (φ : OQ7Prescribed.Position → ℝ)
    · simp [exteriorHessianEntry, Set.indicator, hs hx, Complex.real_smul, mul_comm]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [hL, hR, integral_complex_ofReal, integral_complex_ofReal,
    newton_double_ibp_away φ hr hs]

end QuarticMaxwell.StaticOffSupport

namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed SphereStatic MeasureTheory Set

theorem correlation_zero_near (p : CompactPolarization) (φ : ScalarTest)
    (D : Set OQ7Prescribed.Position) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hsep : ∀ x ∈ tsupport (φ : OQ7Prescribed.Position → ℝ), ∀ y ∈ D, d ≤ ‖x - y‖)
    (j : Fin 3) (z : OQ7Prescribed.Position) (hz : ‖z‖ < d) :
    newtonCurrentCorrelation p φ j z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hp] with y hy
  by_cases hm : y ∈ D
  · have hφ : φ (z + y) = 0 := by
      by_contra hn
      have hd := hsep (z + y) (subset_tsupport φ hn) y hm
      rw [add_sub_cancel_right] at hd
      exact (not_lt_of_ge hd) hz
    simp [hφ]
  · simp [hy hm]

theorem correlation_tsupport_separated (p : CompactPolarization) (φ : ScalarTest)
    (D : Set OQ7Prescribed.Position) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hsep : ∀ x ∈ tsupport (φ : OQ7Prescribed.Position → ℝ), ∀ y ∈ D, d ≤ ‖x - y‖)
    (j : Fin 3) :
    tsupport (newtonCurrentCorrelation p φ j) ⊆ {z | d ≤ ‖z‖} := by
  apply closure_minimal
  · intro z hz
    exact le_of_not_gt (fun hn => hz (correlation_zero_near p φ D hp hsep j z hn))
  · exact isClosed_le continuous_const continuous_norm

theorem realCorrelation_tsupport_separated (L : ℂ →L[ℝ] ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (D : Set OQ7Prescribed.Position) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ tsupport (φ : OQ7Prescribed.Position → ℝ), ∀ y ∈ D, d ≤ ‖x - y‖) (j : Fin 3) :
    tsupport (currentCorrelationRealTest L p φ j : OQ7Prescribed.Position → ℝ) ⊆ {z | d / 2 < ‖z‖} := by
  have hs : tsupport (currentCorrelationRealTest L p φ j : OQ7Prescribed.Position → ℝ) ⊆
      tsupport (newtonCurrentCorrelation p φ j) :=
    tsupport_comp_subset L.map_zero _
  intro z hz
  have hn := correlation_tsupport_separated p φ D hp hsep j (hs hz)
  exact lt_of_lt_of_le (by linarith : d / 2 < d) hn

theorem potentialComponent_separated_hessian (p : CompactPolarization) (φ : ScalarTest)
    (D : Set OQ7Prescribed.Position) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ tsupport (φ : OQ7Prescribed.Position → ℝ), ∀ y ∈ D, d ≤ ‖x - y‖)
    (l i j : Fin 3) :
    potentialComponentDistribution 0 p l (testPartial j (testPartial i φ)) =
      ∫ z : OQ7Prescribed.Position, newtonCurrentCorrelation p φ l z * exteriorHessianEntry (d / 2) i j z := by
  have he : potentialComponentDistribution 0 p l (testPartial j (testPartial i φ)) =
      ∫ z : OQ7Prescribed.Position, newtonCurrentCorrelation p (testPartial j (testPartial i φ)) l z * outgoingGreen 0 z := by
    rw [potentialComponentDistribution_newton_pairing]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => mul_comm _ _)
  rw [he, currentCorrelation_pairing_re_im p _ l (outgoingGreen_locallyIntegrable 0),
    currentCorrelation_pairing_re_im p φ l (exteriorHessianEntry_locallyIntegrable (by linarith) i j)]
  simp_rw [← currentCorrelationRealTest_partial]
  rw [scalarNewton_double_ibp_away _ (by linarith)
      (realCorrelation_tsupport_separated Complex.reCLM p φ D hp hd hsep l),
    scalarNewton_double_ibp_away _ (by linarith)
      (realCorrelation_tsupport_separated Complex.imCLM p φ D hp hd hsep l)]

end QuarticMaxwell.StaticOffSupport

namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed MeasureTheory Set

theorem bounded_kernel_test_joint (p : CompactPolarization) (φ : ScalarTest) (i : Fin 3)
    (K : OQ7Prescribed.Position → ℂ) (hK : Measurable K) {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) :
    Integrable (fun q : OQ7Prescribed.Position × OQ7Prescribed.Position =>
      (φ q.1 : ℂ) * K (q.1 - q.2) * p.current q.2 i) (volume.prod volume) := by
  have hi : Integrable (fun x : OQ7Prescribed.Position => (φ x : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
  have hb := hi.mul_prod (current_component_integrable p i)
  have hm : AEStronglyMeasurable (fun q : OQ7Prescribed.Position × OQ7Prescribed.Position => K (q.1 - q.2))
      (volume.prod volume) :=
    (hK.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  apply (hb.bdd_mul hm (ae_of_all _ (fun q => hC (q.1 - q.2)))).congr
  exact ae_of_all _ (fun _ => by ring)

theorem bounded_kernel_correlation_joint (p : CompactPolarization) (φ : ScalarTest) (i : Fin 3)
    (K : OQ7Prescribed.Position → ℂ) (hK : Measurable K) {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) :
    Integrable (fun q : OQ7Prescribed.Position × OQ7Prescribed.Position =>
      (φ (q.1 + q.2) : ℂ) * K q.1 * p.current q.2 i) (volume.prod volume) := by
  have hi := bounded_kernel_test_joint p φ i K hK hC
  have h := (measurePreserving_add_prod (volume : Measure OQ7Prescribed.Position) volume).integrable_comp
    hi.aestronglyMeasurable |>.mpr hi
  simpa only [Function.comp_def, add_sub_cancel_right] using h

theorem bounded_kernel_correlation_pairing (p : CompactPolarization) (φ : ScalarTest) (i : Fin 3)
    (K : OQ7Prescribed.Position → ℂ) (hK : Measurable K) {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) :
    (∫ z : OQ7Prescribed.Position, newtonCurrentCorrelation p φ i z * K z) =
      ∫ x : OQ7Prescribed.Position, (φ x : ℂ) * ∫ y : OQ7Prescribed.Position, K (x - y) * p.current y i := by
  calc
    _ = ∫ z : OQ7Prescribed.Position, ∫ y : OQ7Prescribed.Position, (φ (z + y) : ℂ) * K z * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        unfold newtonCurrentCorrelation
        change (∫ y : OQ7Prescribed.Position, p.current y i * (φ (z + y) : ℂ)) * K z = _
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring))
    _ = ∫ y : OQ7Prescribed.Position, ∫ z : OQ7Prescribed.Position, (φ (z + y) : ℂ) * K z * p.current y i :=
      integral_integral_swap (bounded_kernel_correlation_joint p φ i K hK hC)
    _ = ∫ y : OQ7Prescribed.Position, ∫ x : OQ7Prescribed.Position, (φ x : ℂ) * K (x - y) * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        have h := integral_add_right_eq_self (μ := (volume : Measure OQ7Prescribed.Position))
          (fun x : OQ7Prescribed.Position => (φ x : ℂ) * K (x - y) * p.current y i) y
        simpa only [add_sub_cancel_right] using h)
    _ = ∫ x : OQ7Prescribed.Position, ∫ y : OQ7Prescribed.Position, (φ x : ℂ) * K (x - y) * p.current y i :=
      (integral_integral_swap (bounded_kernel_test_joint p φ i K hK hC)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change (∫ y : OQ7Prescribed.Position, (φ x : ℂ) * K (x - y) * p.current y i) =
          (φ x : ℂ) * ∫ y : OQ7Prescribed.Position, K (x - y) * p.current y i
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring))

end QuarticMaxwell.StaticOffSupport

namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed MeasureTheory Set
open scoped Convolution

def scalarKernelField (p : CompactPolarization) (K : OQ7Prescribed.Position → ℂ) (i : Fin 3)
    (x : OQ7Prescribed.Position) : ℂ := ∫ y : OQ7Prescribed.Position, K (x - y) * p.current y i

theorem scalarKernelField_integrable (p : CompactPolarization) (K : OQ7Prescribed.Position → ℂ)
    (hK : Measurable K) {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) (i : Fin 3) (x : OQ7Prescribed.Position) :
    Integrable (fun y : OQ7Prescribed.Position => K (x - y) * p.current y i) volume :=
  (current_component_integrable p i).bdd_mul
    (hK.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (ae_of_all _ (fun y => hC (x - y)))

theorem scalarKernelField_aestronglyMeasurable (p : CompactPolarization) (K : OQ7Prescribed.Position → ℂ)
    (hK : Measurable K) (i : Fin 3) :
    AEStronglyMeasurable (scalarKernelField p K i) volume := by
  have hm := (current_component_integrable p i).aestronglyMeasurable.convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hK.aestronglyMeasurable
  apply hm.congr
  exact ae_of_all _ (fun x => by
    change (∫ y : OQ7Prescribed.Position, p.current y i * K (x - y)) = _
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => mul_comm _ _))

theorem scalarKernelField_norm_le (p : CompactPolarization) (K : OQ7Prescribed.Position → ℂ)
    (hK : Measurable K) {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) (i : Fin 3) (x : OQ7Prescribed.Position) :
    ‖scalarKernelField p K i x‖ ≤ C * ∫ y : OQ7Prescribed.Position, ‖p.current y i‖ := by
  calc
    _ ≤ ∫ y : OQ7Prescribed.Position, ‖K (x - y) * p.current y i‖ := norm_integral_le_integral_norm _
    _ ≤ _ := by
      rw [← integral_const_mul]
      apply integral_mono_ae (scalarKernelField_integrable p K hK hC i x).norm
        ((current_component_integrable p i).norm.const_mul C)
      exact ae_of_all _ (fun y => (norm_mul _ _).trans_le
        (mul_le_mul_of_nonneg_right (hC (x - y)) (norm_nonneg _)))

theorem scalarKernelField_locallyIntegrable (p : CompactPolarization) (K : OQ7Prescribed.Position → ℂ)
    (hK : Measurable K) {C : ℝ} (hC : ∀ x, ‖K x‖ ≤ C) (i : Fin 3) :
    LocallyIntegrable (scalarKernelField p K i) volume := by
  rw [locallyIntegrable_iff]
  intro T hT
  exact Measure.integrableOn_of_bounded hT.measure_lt_top.ne
    (scalarKernelField_aestronglyMeasurable p K hK i)
    (ae_of_all _ (scalarKernelField_norm_le p K hK hC i))

def separatedStaticComponent (p : CompactPolarization) (r : ℝ) (i : Fin 3)
    (x : OQ7Prescribed.Position) : ℂ :=
  ∑ j : Fin 3, scalarKernelField p (exteriorHessianEntry r i j) j x

theorem separatedStaticComponent_locallyIntegrable (p : CompactPolarization) {r : ℝ}
    (hr : 0 < r) (i : Fin 3) :
    LocallyIntegrable (separatedStaticComponent p r i) volume := by
  exact locallyIntegrable_finsetSum _ (fun j _ => scalarKernelField_locallyIntegrable p
    (exteriorHessianEntry r i j) (exteriorHessianEntry_measurable r i j)
    (exteriorHessianEntry_bound hr i j) j)

end QuarticMaxwell.StaticOffSupport

namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed MeasureTheory Set

theorem vectorL2ComponentDistribution_integral (f : VectorL2) (φ : ScalarTest) (i : Fin 3) :
    vectorL2ComponentDistribution f i φ = ∫ x : OQ7Prescribed.Position, (φ x : ℂ) * f x i := by
  rw [vectorL2ComponentDistribution_apply]
  have h := (vectorCoordinate i).integral_comp_comm
    (φ.integrable_smul ((vectorL2_locallyIntegrable f).locallyIntegrableOn _))
  exact h.symm

theorem staticFourier_test_separated (p : CompactPolarization) (φ : ScalarTest)
    (D : Set OQ7Prescribed.Position) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ tsupport (φ : OQ7Prescribed.Position → ℝ), ∀ y ∈ D, d ≤ ‖x - y‖) (i : Fin 3) :
    (∫ x : OQ7Prescribed.Position, (φ x : ℂ) * staticFourierOperator (p.memLp.toLp p.current) x i) =
      ∫ x : OQ7Prescribed.Position, (φ x : ℂ) * separatedStaticComponent p (d / 2) i x := by
  rw [← vectorL2ComponentDistribution_integral,
    ← outgoingVolumeDistribution_zero_eq_staticFourier]
  have hvol : outgoingVolumeDistribution 0 p i φ =
      ∑ j : Fin 3, potentialComponentDistribution 0 p j (testPartial j (testPartial i φ)) := by
    simp [outgoingVolumeDistribution, distributionPartial, testPartial,
      Distribution.lineDerivCLM_apply]
  rw [hvol]
  simp_rw [potentialComponent_separated_hessian p φ D hp hd hsep]
  simp_rw [bounded_kernel_correlation_pairing p φ _ _
    (exteriorHessianEntry_measurable (d / 2) _ _)
    (exteriorHessianEntry_bound (by linarith) _ _)]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      simp only [separatedStaticComponent, scalarKernelField, Finset.mul_sum])
  · intro j _
    have hi := φ.integrable_smul
      ((scalarKernelField_locallyIntegrable p (exteriorHessianEntry (d / 2) i j)
        (exteriorHessianEntry_measurable _ _ _)
        (exteriorHessianEntry_bound (by linarith) _ _) j).locallyIntegrableOn _)
    convert hi using 1
    funext x
    simp only [Complex.real_smul]
    rfl

theorem staticFourier_separated_ae (p : CompactPolarization) (D U : Set OQ7Prescribed.Position)
    (hU : IsOpen U) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hd : 0 < d) (hsep : ∀ x ∈ U, ∀ y ∈ D, d ≤ ‖x - y‖) (i : Fin 3) :
    ∀ᵐ x ∂volume, x ∈ U →
      staticFourierOperator (p.memLp.toLp p.current) x i =
        separatedStaticComponent p (d / 2) i x := by
  let f : VectorL2 := staticFourierOperator (p.memLp.toLp p.current)
  have hfi : LocallyIntegrableOn (fun x : OQ7Prescribed.Position => f x i) U volume :=
    (vectorCoordinate i).locallyIntegrableOn_comp ((vectorL2_locallyIntegrable f).locallyIntegrableOn U)
  have hgi := (separatedStaticComponent_locallyIntegrable p (by linarith : 0 < d / 2) i).locallyIntegrableOn U
  have htest : ∀ (g : OQ7Prescribed.Position → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ U → ∫ x, g x • (f x i - separatedStaticComponent p (d / 2) i x) = 0 := by
    intro g hg hc hs
    let φ : ScalarTest := ⟨g, hg, hc, subset_univ _⟩
    have he := staticFourier_test_separated p φ D hp hd (fun x hx => hsep x (hs hx)) i
    have hfglobal := (vectorCoordinate i).locallyIntegrableOn_comp
      ((vectorL2_locallyIntegrable f).locallyIntegrableOn (⊤ : TopologicalSpace.Opens OQ7Prescribed.Position))
    have hgglobal := (separatedStaticComponent_locallyIntegrable p (by linarith : 0 < d / 2) i).locallyIntegrableOn
      (⊤ : TopologicalSpace.Opens OQ7Prescribed.Position)
    change (∫ x, φ x • (f x i - separatedStaticComponent p (d / 2) i x)) = 0
    simp_rw [smul_sub]
    have hfi' : Integrable (fun x : OQ7Prescribed.Position => φ x • f x i) volume :=
      φ.integrable_smul hfglobal
    rw [integral_sub hfi' (φ.integrable_smul hgglobal)]
    simp only [Complex.real_smul]
    exact sub_eq_zero.mpr he
  filter_upwards [hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hfi.sub hgi) htest] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

end QuarticMaxwell.StaticOffSupport

namespace QuarticMaxwell.StaticOffSupport
open OQ7Prescribed MeasureTheory Set

def exteriorHessian (r : ℝ) : OQ7Prescribed.Position → Vector →L[ℂ] Vector :=
  {x : OQ7Prescribed.Position | r < ‖x‖}.indicator StaticHessian.newtonHessianOperator

theorem exteriorHessian_measurable (r : ℝ) : Measurable (exteriorHessian r) :=
  StaticHessian.newtonHessianOperator_measurable.indicator
    (isOpen_lt continuous_const continuous_norm).measurableSet

theorem exteriorHessian_apply (r : ℝ) (x : OQ7Prescribed.Position) (v : Vector) (i : Fin 3) :
    exteriorHessian r x v i = ∑ j, exteriorHessianEntry r i j x * v j := by
  by_cases hx : r < ‖x‖
  · simp [exteriorHessian, exteriorHessianEntry, Set.indicator, hx,
      StaticHessian.newtonHessianOperator_apply]
  · simp [exteriorHessian, exteriorHessianEntry, Set.indicator, hx]

theorem exteriorHessian_norm_le {r : ℝ} (hr : 0 < r) (x : OQ7Prescribed.Position) :
    ‖exteriorHessian r x‖ ≤ 1 / (2 * Real.pi * r ^ 3) := by
  by_cases hx : r < ‖x‖
  · simp only [exteriorHessian, Set.indicator, Set.mem_ofPred_eq, hx, ite_true]
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans hr hx))
    apply (StaticHessian.newtonHessianOperator_norm_le x hx0).trans
    gcongr
  · simp only [exteriorHessian, Set.indicator, Set.mem_ofPred_eq, hx, ite_false, norm_zero]
    positivity

def vectorKernelField (p : CompactPolarization) (r : ℝ) (x : OQ7Prescribed.Position) : Vector :=
  ∫ y : OQ7Prescribed.Position, exteriorHessian r (x - y) (p.current y)

theorem vectorKernelField_integrable (p : CompactPolarization) {r : ℝ} (hr : 0 < r) (x : OQ7Prescribed.Position) :
    Integrable (fun y : OQ7Prescribed.Position => exteriorHessian r (x - y) (p.current y)) volume := by
  have hm : AEStronglyMeasurable (fun y : OQ7Prescribed.Position => exteriorHessian r (x - y) (p.current y)) volume :=
    (ContinuousLinearMap.apply ℂ Vector).aestronglyMeasurable_comp₂
      p.memLp.aestronglyMeasurable
      ((exteriorHessian_measurable r).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  apply Integrable.mono' ((compactPolarization_current_integrable p).norm.const_mul
    (1 / (2 * Real.pi * r ^ 3))) hm
  exact ae_of_all _ (fun y => ((exteriorHessian r (x - y)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (exteriorHessian_norm_le hr (x - y)) (norm_nonneg _)))

theorem vectorKernelField_component (p : CompactPolarization) {r : ℝ} (hr : 0 < r)
    (x : OQ7Prescribed.Position) (i : Fin 3) :
    vectorKernelField p r x i = separatedStaticComponent p r i x := by
  have h := (vectorCoordinate i).integral_comp_comm (vectorKernelField_integrable p hr x)
  change (∫ y : OQ7Prescribed.Position, exteriorHessian r (x - y) (p.current y) i) = vectorKernelField p r x i at h
  rw [← h]
  simp_rw [exteriorHessian_apply]
  rw [integral_finsetSum]
  · rfl
  · intro j _
    exact scalarKernelField_integrable p (exteriorHessianEntry r i j)
      (exteriorHessianEntry_measurable r i j) (exteriorHessianEntry_bound hr i j) j x

theorem staticFourier_vector_separated_ae (p : CompactPolarization) (D U : Set OQ7Prescribed.Position)
    (hU : IsOpen U) (hp : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0)
    {d : ℝ} (hd : 0 < d) (hsep : ∀ x ∈ U, ∀ y ∈ D, d ≤ ‖x - y‖) :
    ∀ᵐ x ∂volume, x ∈ U →
      staticFourierOperator (p.memLp.toLp p.current) x = vectorKernelField p (d / 2) x := by
  have h := fun i : Fin 3 => staticFourier_separated_ae p D U hU hp hd hsep i
  filter_upwards [ae_all_iff.mpr h] with x hx hmem
  apply PiLp.ext
  intro i
  exact (hx i hmem).trans (vectorKernelField_component p (by linarith) x i).symm

end QuarticMaxwell.StaticOffSupport


