import QuarticMaxwell.SphereNewton
import QuarticMaxwell.StaticInverse
import PrescribedExtinction.NewtonStaticIdentification
import PrescribedExtinction.NewtonCutoffIBP
import PrescribedExtinction.SmoothOutgoingFields
import PrescribedExtinction.DistributionVectorCalculus

/-! Actual constant-current ball response for the physical static Fourier
operator. The Newton potential formula is derived by volume integration in
SphereNewton, not posited as an electrostatic response certificate. -/
noncomputable section
namespace QuarticMaxwell
namespace SphereStatic
open OQ7Prescribed SphereNewton MeasureTheory Set
open scoped Matrix Convolution Topology

def zDirection : UnitSphere := ⟨basisR 2, by simp [basisR]⟩

theorem ball_measure_ne_top (c : OQ7Prescribed.Position) (a : ℝ) :
    volume (Metric.ball c a) ≠ ⊤ :=
  ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall c a).measure_lt_top).ne

def ballSource (c : OQ7Prescribed.Position) (a : ℝ) (v : Vector) : DomainL2 (Metric.ball c a) :=
  domainIncidentSource 0 zDirection v (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a)

theorem ballSource_coe (c : OQ7Prescribed.Position) (a : ℝ) (v : Vector) :
    (ballSource c a v : VectorL2) =ᵐ[volume] (Metric.ball c a).indicator (fun _ => v) := by
  have h := incidentSource_coe 0 zDirection v (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a)
  have hw : incidentWave 0 zDirection v = (fun _ => v) := by
    funext x
    simp [incidentWave, radiationPhase]
  simpa only [ballSource, domainIncidentSource, hw] using h

theorem ball_support_bound (c : OQ7Prescribed.Position) (a : ℝ) :
    Metric.ball c a ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) (‖c‖ + a) := by
  intro x hx
  have hxc : ‖x - c‖ < a := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hnorm : ‖x‖ ≤ ‖x - c‖ + ‖c‖ := by
    calc
      _ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

def ballPolarization (c : OQ7Prescribed.Position) (a : ℝ) (ha : 0 ≤ a) (v : Vector) : CompactPolarization :=
  domainPolarization (Metric.ball c a) measurableSet_ball (by positivity : 0 ≤ ‖c‖ + a)
    (ball_support_bound c a) (ballSource c a v)

theorem ballPolarization_current (c : OQ7Prescribed.Position) (a : ℝ) (ha : 0 ≤ a) (v : Vector) :
    (ballPolarization c a ha v).current =ᵐ[volume] (Metric.ball c a).indicator (fun _ => v) :=
  (domainPolarization_current_ae _ measurableSet_ball (by positivity) (ball_support_bound c a)
    (ballSource c a v)).trans (ballSource_coe c a v)

def shiftedNewtonPotential (c : OQ7Prescribed.Position) (a : ℝ) (x : OQ7Prescribed.Position) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ y in Metric.ball c a, ‖y - x‖⁻¹

theorem shiftedNewtonPotential_eq (c : OQ7Prescribed.Position) (a : ℝ) (x : OQ7Prescribed.Position) :
    shiftedNewtonPotential c a x = ballNewtonPotential a (x - c) := by
  unfold shiftedNewtonPotential ballNewtonPotential
  congr 1
  have h := integral_add_right_eq_self (μ := (volume : Measure OQ7Prescribed.Position))
    ((Metric.ball c a).indicator (fun y : OQ7Prescribed.Position => ‖y - x‖⁻¹)) c
  have heq : (fun y : OQ7Prescribed.Position => (Metric.ball c a).indicator
      (fun z : OQ7Prescribed.Position => ‖z - x‖⁻¹) (y + c)) =
      (Metric.ball 0 a).indicator (fun y => ‖y - (x - c)‖⁻¹) := by
    funext y
    simp [Set.indicator, Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [heq, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at h
  exact h.symm

theorem outgoingPotential_ball (c : OQ7Prescribed.Position) {a : ℝ} (ha : 0 ≤ a) (v : Vector)
    (x : OQ7Prescribed.Position) :
    outgoingPotential 0 (ballPolarization c a ha v) x =
      (shiftedNewtonPotential c a x : ℂ) • v := by
  have hcur := ballPolarization_current c a ha v
  change (∫ y : OQ7Prescribed.Position,
    outgoingGreen 0 (x - y) • (ballPolarization c a ha v).current y) = _
  have heq : (∫ y : OQ7Prescribed.Position,
      outgoingGreen 0 (x - y) • (ballPolarization c a ha v).current y) =
      ∫ y in Metric.ball c a, outgoingGreen 0 (x - y) • v := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [hcur] with y hy
    rw [hy]
    by_cases hmem : y ∈ Metric.ball c a <;> simp [Set.indicator, hmem]
  rw [heq, integral_smul_const]
  congr 1
  have hk : (fun y : OQ7Prescribed.Position => outgoingGreen 0 (x - y)) =
      (fun y => (((4 * Real.pi)⁻¹ * ‖y - x‖⁻¹ : ℝ) : ℂ)) := by
    funext y
    rw [outgoingGreen_zero_eq_newton]
    simp only [newtonRadial, norm_sub_rev]
  rw [hk]
  have hi := (newton_bounded_support_integrable (Metric.ball c a)
    (ball_support_bound c a) x).const_mul (4 * Real.pi)⁻¹
  calc
    _ = ((∫ y in Metric.ball c a, (4 * Real.pi)⁻¹ * ‖y - x‖⁻¹ : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hi
    _ = _ := by rw [integral_const_mul]; rfl

end SphereStatic
end QuarticMaxwell

namespace QuarticMaxwell.SphereStatic
open OQ7Prescribed MeasureTheory Set

def interiorPotential (c : Position) (a : ℝ) (x : Position) : ℝ :=
  (3 * a ^ 2 - ‖x - c‖ ^ 2) / 6

theorem interiorPotential_contDiff (c : Position) (a : ℝ) :
    ContDiff ℝ 1 (interiorPotential c a) :=
  (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).div_const 6

theorem interiorPotential_hasLineDerivAt (c : Position) (a : ℝ) (i : Fin 3) (x : Position) :
    HasLineDerivAt ℝ (interiorPotential c a) (-(x i - c i) / 3) x (basisR i) := by
  have h := ((hasFDerivAt_const (3 * a ^ 2) x).sub
    ((hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const c))).const_mul (1 / 6 : ℝ) |>.hasLineDerivAt (basisR i)
  convert h using 1
  · funext y
    simp [interiorPotential, div_eq_mul_inv, mul_comm]
  · simp [real_inner_basis]
    ring

theorem interiorPotential_lineDeriv (c : Position) (a : ℝ) (i : Fin 3) (x : Position) :
    lineDeriv ℝ (interiorPotential c a) x (basisR i) = -(x i - c i) / 3 :=
  (interiorPotential_hasLineDerivAt c a i x).lineDeriv

def interiorGradient (c : Position) (i : Fin 3) (x : Position) : ℝ := -(x i - c i) / 3

theorem interiorGradient_contDiff (c : Position) (i : Fin 3) :
    ContDiff ℝ 1 (interiorGradient c i) :=
  (((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : Position →L[ℝ] ℝ).contDiff.sub
    contDiff_const).neg).div_const 3

theorem interiorGradient_lineDeriv (c : Position) (i j : Fin 3) (x : Position) :
    lineDeriv ℝ (interiorGradient c i) x (basisR j) = -(if i = j then 1 else 0) / 3 := by
  have h := (((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : Position →L[ℝ] ℝ).hasFDerivAt
    (x := x)).sub_const (c i)).neg.const_mul (1 / 3 : ℝ) |>.hasLineDerivAt (basisR j)
  have he : interiorGradient c i = (fun y : Position => 1 / 3 * (-(y i - c i))) := by
    funext y
    simp [interiorGradient, div_eq_mul_inv, mul_comm]
  rw [he]
  convert h.lineDeriv using 1
  · congr 1
  · by_cases hij : i = j <;> norm_num [basisR, hij]

theorem testPartial_tsupport (i : Fin 3) (φ : ScalarTest) :
    tsupport (testPartial i φ : Position → ℝ) ⊆ tsupport (φ : Position → ℝ) := by
  have he : (testPartial i φ : Position → ℝ) =
      (fun x => fderiv ℝ (φ : Position → ℝ) x (basisR i)) := by
    funext x
    exact testPartial_eq_fderiv φ i x
  rw [he]
  exact tsupport_fderiv_apply_subset ℝ (basisR i)

end QuarticMaxwell.SphereStatic


namespace QuarticMaxwell.SphereStatic
open OQ7Prescribed MeasureTheory Set

theorem interiorPotential_test_second (c : Position) (a : ℝ) (i j : Fin 3) (φ : ScalarTest) :
    (∫ x, interiorPotential c a x * (testPartial j (testPartial i φ)) x) =
      (-(if i = j then 1 else 0) / 3) * ∫ x, φ x := by
  rw [contDiff_test_ibp _ (interiorPotential_contDiff c a) (testPartial i φ) j]
  simp_rw [interiorPotential_lineDeriv]
  change -(∫ x, interiorGradient c j x * (testPartial i φ) x) = _
  rw [contDiff_test_ibp _ (interiorGradient_contDiff c j) φ i]
  simp_rw [interiorGradient_lineDeriv, eq_comm]
  rw [neg_neg, integral_const_mul]

theorem outgoingPotential_ball_interior (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (x : Position) (hx : x ∈ Metric.ball c a) :
    outgoingPotential 0 (ballPolarization c a ha.le v) x =
      (interiorPotential c a x : ℂ) • v := by
  rw [outgoingPotential_ball c ha.le, shiftedNewtonPotential_eq,
    SphereNewton.ballNewton_interior ha (x - c)
      (by exact (show ‖x - c‖ < a from by simpa only [Metric.mem_ball, dist_eq_norm] using hx).le)]
  rfl

theorem potentialPairing_ball (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (φ : ScalarTest) (hs : tsupport (φ : Position → ℝ) ⊆ Metric.ball c a) :
    (∫ x : Position, φ x • outgoingPotential 0 (ballPolarization c a ha.le v) x) =
      ((∫ x : Position, interiorPotential c a x * φ x : ℝ) : ℂ) • v := by
  have he : (fun x : Position => φ x • outgoingPotential 0 (ballPolarization c a ha.le v) x) =
      (fun x => (((interiorPotential c a x * φ x : ℝ) : ℂ)) • v) := by
    funext x
    by_cases hx : x ∈ tsupport (φ : Position → ℝ)
    · rw [outgoingPotential_ball_interior c ha v x (hs hx)]
      rw [← IsScalarTower.algebraMap_smul ℂ (φ x)]
      simp only [Algebra.algebraMap_eq_smul_one, Complex.real_smul,
        mul_one, smul_smul, Complex.ofReal_mul]
      rw [mul_comm]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [he, integral_smul_const]
  congr 1
  have hi : Integrable (fun x : Position => interiorPotential c a x * φ x) volume :=
    ((interiorPotential_contDiff c a).continuous.mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  exact Complex.ofRealCLM.integral_comp_comm hi

end QuarticMaxwell.SphereStatic


namespace QuarticMaxwell.SphereStatic
open OQ7Prescribed MeasureTheory Set

theorem outgoingVolume_ball_test (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (φ : ScalarTest) (hs : tsupport (φ : Position → ℝ) ⊆ Metric.ball c a) (i : Fin 3) :
    outgoingVolumeDistribution 0 (ballPolarization c a ha.le v) i φ =
      (-((∫ x : Position, φ x : ℝ) : ℂ) / 3) * v i := by
  rw [outgoingVolumeDistribution_apply]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, zero_add]
  have hp (j : Fin 3) := potentialPairing_ball c ha v (testPartial j (testPartial i φ))
    ((testPartial_tsupport j _).trans ((testPartial_tsupport i _).trans hs))
  simp_rw [hp, interiorPotential_test_second]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, neg_div, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_mul]
    ring
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem staticFourier_ball_test (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    (φ : ScalarTest) (hs : tsupport (φ : Position → ℝ) ⊆ Metric.ball c a) :
    (∫ x : Position, φ x • staticFourierOperator (ballSource c a v : VectorL2) x) =
      (-((∫ x : Position, φ x : ℝ) : ℂ) / 3) • v := by
  apply PiLp.ext
  intro i
  have h := outgoingVolume_ball_test c ha v φ hs i
  rw [outgoingVolumeDistribution_zero_eq_staticFourier, vectorL2ComponentDistribution_apply] at h
  have hto : (ballPolarization c a ha.le v).memLp.toLp (ballPolarization c a ha.le v).current =
      (ballSource c a v : VectorL2) :=
    domainPolarization_toLp _ measurableSet_ball (by positivity) (ball_support_bound c a) _
  simpa only [hto, PiLp.smul_apply, smul_eq_mul] using h

end QuarticMaxwell.SphereStatic

namespace QuarticMaxwell.SphereStatic
open OQ7Prescribed MeasureTheory Set

theorem staticFourier_ball_interior (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) :
    ∀ᵐ x ∂volume, x ∈ Metric.ball c a →
      staticFourierOperator (ballSource c a v : VectorL2) x = (-1 / 3 : ℂ) • v := by
  let f : VectorL2 := staticFourierOperator (ballSource c a v : VectorL2)
  have hf := (vectorL2_locallyIntegrable f).add
    (locallyIntegrable_const ((1 / 3 : ℂ) • v))
  have hz := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrableOn (Metric.ball c a))
  have htest : ∀ (g : Position → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Metric.ball c a → ∫ x, g x • (f x + (1 / 3 : ℂ) • v) = 0 := by
    intro g hg hc hs
    let φ : ScalarTest := ⟨g, hg, hc, subset_univ _⟩
    have h := staticFourier_ball_test c ha v φ hs
    have hfi : Integrable (fun x : Position => φ x • f x) volume :=
      φ.integrable_smul ((vectorL2_locallyIntegrable f).locallyIntegrableOn _)
    have hci : Integrable (fun x : Position => φ x • ((1 / 3 : ℂ) • v)) volume :=
      φ.integrable_smul ((locallyIntegrable_const ((1 / 3 : ℂ) • v)).locallyIntegrableOn _)
    change (∫ x, φ x • (f x + (1 / 3 : ℂ) • v)) = 0
    simp_rw [smul_add]
    rw [integral_add hfi hci, h, integral_smul_const, ← smul_assoc]
    rw [Complex.real_smul]
    rw [← add_smul]
    have hcoef : (-((∫ x : Position, φ x : ℝ) : ℂ) / 3) +
      ((∫ x : Position, φ x : ℝ) : ℂ) * (1 / 3 : ℂ) = 0 := by ring
    rw [hcoef, zero_smul]
  filter_upwards [hz htest] with x hx hmem
  have he := hx hmem
  change f x + (1 / 3 : ℂ) • v = 0 at he
  have hneg : f x = -((1 / 3 : ℂ) • v) := eq_neg_of_add_eq_zero_left he
  simpa only [neg_smul, neg_div] using hneg

end QuarticMaxwell.SphereStatic

namespace QuarticMaxwell.SphereStatic
open OQ7Prescribed MeasureTheory Set

theorem domainStatic_ballSource (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) :
    domainStaticOperator (Metric.ball c a) measurableSet_ball (ballSource c a v) =
      (-1 / 3 : ℂ) • ballSource c a v := by
  apply Subtype.ext
  rw [domainStaticOperator_coe]
  change supportRestrictionCLM (Metric.ball c a) measurableSet_ball
    (staticFourierOperator (supportRestrictionCLM (Metric.ball c a) measurableSet_ball
      (ballSource c a v : VectorL2))) = _
  rw [supportRestrictionCLM_eq_self]
  apply Lp.ext
  filter_upwards [indicatorL2_coe volume (Metric.ball c a) measurableSet_ball
      (staticFourierOperator (ballSource c a v : VectorL2)),
    staticFourier_ball_interior c ha v, ballSource_coe c a v,
    Lp.coeFn_smul (-1 / 3 : ℂ) (ballSource c a v : VectorL2)] with x hmask hstatic hsource hsmul
  change (indicatorL2 volume (Metric.ball c a) measurableSet_ball
      (staticFourierOperator (ballSource c a v : VectorL2))) x = _
  rw [hmask]
  change _ = ((-1 / 3 : ℂ) • (ballSource c a v : VectorL2)) x
  rw [hsmul]
  simp only [Pi.smul_apply, hsource]
  by_cases hx : x ∈ Metric.ball c a
  · simp [Set.indicator, hx, hstatic hx]
  · simp [Set.indicator, hx]

end QuarticMaxwell.SphereStatic
