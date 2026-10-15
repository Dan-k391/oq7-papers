import QuarticMaxwell.SphereStatic
import QuarticMaxwell.StaticOffSupport

/-! The exterior field of an actual uniformly polarized finite ball.
It is derived from the volume Newton potential and compact-test identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QuarticMaxwell.SphereExterior
open OQ7Prescribed SphereStatic StaticOffSupport StaticHessian MeasureTheory Set

def translateTest (c : Position) (φ : ScalarTest) : ScalarTest where
  toFun x := φ (x + c)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight c)
  tsupport_subset' := subset_univ _

theorem translateTest_partial (c : Position) (φ : ScalarTest) (i : Fin 3) :
    testPartial i (translateTest c φ) = translateTest c (testPartial i φ) := by
  ext x
  rw [testPartial_eq_fderiv]
  change fderiv ℝ (fun y => φ (y + c)) x (basisR i) = testPartial i φ (x + c)
  rw [fderiv_comp_add_right, testPartial_eq_fderiv]

theorem translateTest_support (c : Position) (φ : ScalarTest) :
    tsupport (translateTest c φ : Position → ℝ) =
      (fun x : Position => x + c) ⁻¹' tsupport (φ : Position → ℝ) :=
  tsupport_comp_eq_preimage (φ : Position → ℝ) (Homeomorph.addRight c)

theorem newton_shifted_double_ibp (c : Position) (φ : ScalarTest) {r : ℝ} (hr : 0 < r)
    (hs : tsupport (φ : Position → ℝ) ⊆ {x | r < ‖x - c‖}) (i j : Fin 3) :
    (∫ x : Position, newtonReal (x - c) * testPartial j (testPartial i φ) x) =
      ∫ x : Position, newtonHessianKernel i j (x - c) * φ x := by
  have hs' : tsupport (translateTest c φ : Position → ℝ) ⊆ {x | r < ‖x‖} := by
    intro x hx
    rw [translateTest_support] at hx
    simpa only [mem_ofPred_eq, mem_preimage, add_sub_cancel_right] using hs hx
  have h := newton_double_ibp_away (translateTest c φ) hr hs' i j
  rw [translateTest_partial, translateTest_partial] at h
  have hL := integral_add_right_eq_self (μ := (volume : Measure Position))
    (fun x : Position => newtonReal (x - c) * testPartial j (testPartial i φ) x) c
  have hR := integral_add_right_eq_self (μ := (volume : Measure Position))
    (fun x : Position => newtonHessianKernel i j (x - c) * φ x) c
  change (∫ x : Position, newtonReal x * testPartial j (testPartial i φ) (x + c)) =
    ∫ x : Position, newtonHessianKernel i j x * φ (x + c) at h
  rw [← hL, ← hR]
  simpa only [add_sub_cancel_right] using h

def ballVolume (a : ℝ) : ℝ := 4 * Real.pi * a ^ 3 / 3

theorem ballVolume_eq_measure (c : Position) (a : ℝ) (ha : 0 ≤ a) :
    ballVolume a = volume.real (Metric.ball c a) := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal (by positivity)]
  unfold ballVolume
  ring

theorem potential_ball_exterior (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (x : Position) (hx : a < ‖x - c‖) :
    outgoingPotential 0 (ballPolarization c a ha.le v) x =
      ((ballVolume a * newtonReal (x - c) : ℝ) : ℂ) • v := by
  rw [outgoingPotential_ball c ha.le, shiftedNewtonPotential_eq,
    SphereNewton.ballNewton_exterior ha (x - c) hx.le]
  congr 2
  unfold ballVolume newtonReal
  field_simp

theorem potentialPairing_ball_exterior (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (φ : ScalarTest) (hs : tsupport (φ : Position → ℝ) ⊆ {x | a < ‖x - c‖}) :
    (∫ x : Position, φ x • outgoingPotential 0 (ballPolarization c a ha.le v) x) =
      ((ballVolume a * ∫ x : Position, newtonReal (x - c) * φ x : ℝ) : ℂ) • v := by
  have he : (fun x : Position => φ x • outgoingPotential 0 (ballPolarization c a ha.le v) x) =
      (fun x => (((ballVolume a * (newtonReal (x - c) * φ x) : ℝ) : ℂ)) • v) := by
    funext x
    by_cases hx : x ∈ tsupport (φ : Position → ℝ)
    · rw [potential_ball_exterior c ha v x (hs hx), ← smul_assoc, Complex.real_smul]
      congr 1
      push_cast
      ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [he, integral_smul_const, integral_complex_ofReal, integral_const_mul]

def exteriorField (c : Position) (a : ℝ) (v : Vector) (x : Position) : Vector :=
  (ballVolume a : ℂ) • exteriorHessian a (x - c) v

theorem exteriorEntry_test_integrable (c : Position) {a : ℝ} (ha : 0 < a)
    (φ : ScalarTest) (i j : Fin 3) :
    Integrable (fun x : Position => (φ x : ℂ) * exteriorHessianEntry a i j (x - c)) volume := by
  have hφ : Integrable (fun x : Position => (φ x : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
  simpa only [Function.comp_apply, Pi.sub_apply, id_eq, mul_comm] using
    hφ.bdd_mul ((exteriorHessianEntry_measurable a i j).comp
    (measurable_id.sub measurable_const)).aestronglyMeasurable
    (ae_of_all _ (fun x => exteriorHessianEntry_bound ha i j (x - c)))

theorem hessianEntry_test_eq (c : Position) (a : ℝ) (φ : ScalarTest)
    (hs : tsupport (φ : Position → ℝ) ⊆ {x | a < ‖x - c‖}) (i j : Fin 3) :
    (((∫ x : Position, newtonHessianKernel i j (x - c) * φ x : ℝ)) : ℂ) =
      ∫ x : Position, (φ x : ℂ) * exteriorHessianEntry a i j (x - c) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change ((newtonHessianKernel i j (x - c) * φ x : ℝ) : ℂ) =
      (φ x : ℂ) * exteriorHessianEntry a i j (x - c)
    by_cases hx : x ∈ tsupport (φ : Position → ℝ)
    · have hx' : a < ‖x - c‖ := hs hx
      simp [exteriorHessianEntry, Set.indicator, hx', mul_comm]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp)

theorem outgoingVolume_ball_exterior_test (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (φ : ScalarTest) (hs : tsupport (φ : Position → ℝ) ⊆ {x | a < ‖x - c‖}) (i : Fin 3) :
    outgoingVolumeDistribution 0 (ballPolarization c a ha.le v) i φ =
      ∫ x : Position, (φ x : ℂ) * exteriorField c a v x i := by
  rw [outgoingVolumeDistribution_apply]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, zero_add]
  have hp (j : Fin 3) := potentialPairing_ball_exterior c ha v (testPartial j (testPartial i φ))
    ((testPartial_tsupport j _).trans ((testPartial_tsupport i _).trans hs))
  simp_rw [hp, newton_shifted_double_ibp c φ ha hs]
  simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp_rw [hessianEntry_test_eq c a φ hs]
  have he (x : Position) : (φ x : ℂ) * exteriorField c a v x i =
      ∑ j : Fin 3, (ballVolume a : ℂ) *
        ((φ x : ℂ) * exteriorHessianEntry a i j (x - c)) * v j := by
    simp only [exteriorField, PiLp.smul_apply, smul_eq_mul, exteriorHessian_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, integral_const_mul]
  · intro j _
    exact ((exteriorEntry_test_integrable c ha φ i j).const_mul (ballVolume a : ℂ)).mul_const (v j)

theorem exteriorField_measurable (c : Position) (a : ℝ) (v : Vector) :
    Measurable (exteriorField c a v) := by
  have hm : Measurable (fun x : Position => exteriorHessian a (x - c)) :=
    (exteriorHessian_measurable a).comp (measurable_id.sub measurable_const)
  have hs : Measurable (fun _ : Position => (ballVolume a : ℂ)) := measurable_const
  exact hs.smul ((ContinuousLinearMap.apply ℂ Vector v).continuous.measurable.comp hm)

theorem exteriorField_norm_le (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) (x : Position) :
    ‖exteriorField c a v x‖ ≤ |ballVolume a| * (1 / (2 * Real.pi * a ^ 3) * ‖v‖) := by
  rw [exteriorField, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact ((exteriorHessian a (x - c)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (exteriorHessian_norm_le ha (x - c)) (norm_nonneg _))

theorem exteriorField_locallyIntegrable (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) :
    LocallyIntegrable (exteriorField c a v) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (exteriorField_measurable c a v).aestronglyMeasurable
    (ae_of_all _ (exteriorField_norm_le c ha v))

theorem staticFourier_ball_exterior_test (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (φ : ScalarTest) (hs : tsupport (φ : Position → ℝ) ⊆ {x | a < ‖x - c‖}) (i : Fin 3) :
    (∫ x : Position, (φ x : ℂ) * staticFourierOperator (ballSource c a v : VectorL2) x i) =
      ∫ x : Position, (φ x : ℂ) * exteriorField c a v x i := by
  have h := outgoingVolume_ball_exterior_test c ha v φ hs i
  rw [outgoingVolumeDistribution_zero_eq_staticFourier, vectorL2ComponentDistribution_apply] at h
  have hto : (ballPolarization c a ha.le v).memLp.toLp (ballPolarization c a ha.le v).current =
      (ballSource c a v : VectorL2) :=
    domainPolarization_toLp _ measurableSet_ball (by positivity) (ball_support_bound c a) _
  rw [hto] at h
  have hi := φ.integrable_smul
    ((vectorL2_locallyIntegrable (staticFourierOperator (ballSource c a v : VectorL2))).locallyIntegrableOn _)
  have hc := (vectorCoordinate i).integral_comp_comm hi
  change (∫ x : Position, (φ x • staticFourierOperator (ballSource c a v : VectorL2) x) i) =
    (∫ x : Position, φ x • staticFourierOperator (ballSource c a v : VectorL2) x) i at hc
  rw [← hc] at h
  simpa only [PiLp.smul_apply, Complex.real_smul, smul_eq_mul] using h

theorem staticFourier_ball_exterior_ae (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) :
    ∀ᵐ x ∂volume, a < ‖x - c‖ →
      staticFourierOperator (ballSource c a v : VectorL2) x =
        (ballVolume a : ℂ) • newtonHessianOperator (x - c) v := by
  let U : Set Position := {x | a < ‖x - c‖}
  have hU : IsOpen U := isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm)
  let f : VectorL2 := staticFourierOperator (ballSource c a v : VectorL2)
  have hi (i : Fin 3) : ∀ᵐ x ∂volume, x ∈ U → f x i = exteriorField c a v x i := by
    have hfi := (vectorCoordinate i).locallyIntegrableOn_comp ((vectorL2_locallyIntegrable f).locallyIntegrableOn U)
    have hgi := (vectorCoordinate i).locallyIntegrableOn_comp ((exteriorField_locallyIntegrable c ha v).locallyIntegrableOn U)
    have htest : ∀ g : Position → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ U → ∫ x, g x • (f x i - exteriorField c a v x i) = 0 := by
      intro g hg hc hs
      let φ : ScalarTest := ⟨g, hg, hc, subset_univ _⟩
      have he := staticFourier_ball_exterior_test c ha v φ hs i
      have hif := (vectorCoordinate i).locallyIntegrableOn_comp
        ((vectorL2_locallyIntegrable f).locallyIntegrableOn (⊤ : TopologicalSpace.Opens Position))
      have hig := (vectorCoordinate i).locallyIntegrableOn_comp
        ((exteriorField_locallyIntegrable c ha v).locallyIntegrableOn (⊤ : TopologicalSpace.Opens Position))
      change LocallyIntegrableOn (fun x : Position => f x i) (⊤ : TopologicalSpace.Opens Position) volume at hif
      change LocallyIntegrableOn (fun x : Position => exteriorField c a v x i)
        (⊤ : TopologicalSpace.Opens Position) volume at hig
      change (∫ x, φ x • (f x i - exteriorField c a v x i)) = 0
      simp_rw [smul_sub]
      rw [integral_sub (φ.integrable_smul hif) (φ.integrable_smul hig)]
      simp only [Complex.real_smul]
      exact sub_eq_zero.mpr he
    filter_upwards [hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hfi.sub hgi) htest] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  filter_upwards [ae_all_iff.mpr hi] with x hx hxa
  have he : f x = exteriorField c a v x := PiLp.ext (fun i => hx i hxa)
  simpa [exteriorField, exteriorHessian, Set.indicator, hxa] using he

end QuarticMaxwell.SphereExterior
