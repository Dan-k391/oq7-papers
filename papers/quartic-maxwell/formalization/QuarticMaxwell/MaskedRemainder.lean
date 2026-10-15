import QuarticMaxwell.ProjectionKernel
import QuarticMaxwell.SharpVolume
import QuarticMaxwell.Schur
import PrescribedExtinction.CompactOutgoingOperator
import PrescribedExtinction.SetSupportedL2
import PrescribedExtinction.OutgoingVolumeIdentification

/-! The actual outgoing-minus-static Maxwell convolution, compressed to an
arbitrary measurable bounded support. No analytic operator norm is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed
open scoped Classical

def maskedDyadicKernel (k : ℝ) (D : Set Position) (z : Position × Position) :
    Vector →L[ℂ] Vector :=
  if z.1 ∈ D ∧ z.2 ∈ D then dyadicRemainder k (z.1 - z.2) else 0

def maskedDyadicMajorant (k : ℝ) (D : Set Position) (z : Position × Position) : ℝ :=
  if z.1 ∈ D ∧ z.2 ∈ D then (3 * k ^ 2 / (8 * Real.pi)) * ‖z.1 - z.2‖⁻¹ else 0

theorem maskedDyadicKernel_measurable (k : ℝ) (D : Set Position) (hD : MeasurableSet D) :
    Measurable (maskedDyadicKernel k D) := by
  have hs : MeasurableSet {z : Position × Position | z.1 ∈ D ∧ z.2 ∈ D} :=
    (hD.preimage measurable_fst).inter (hD.preimage measurable_snd)
  have hm := (dyadicRemainder_measurable k).comp (measurable_fst.sub measurable_snd)
  convert hm.indicator hs using 1
  funext z
  simp [maskedDyadicKernel, indicator]

theorem maskedDyadicMajorant_measurable (k : ℝ) (D : Set Position) (hD : MeasurableSet D) :
    Measurable (maskedDyadicMajorant k D) := by
  have hs : MeasurableSet {z : Position × Position | z.1 ∈ D ∧ z.2 ∈ D} :=
    (hD.preimage measurable_fst).inter (hD.preimage measurable_snd)
  have hm : Measurable (fun z : Position × Position =>
      (3 * k ^ 2 / (8 * Real.pi)) * ‖z.1 - z.2‖⁻¹) := by fun_prop
  convert hm.indicator hs using 1
  funext z
  simp [maskedDyadicMajorant, indicator]

theorem maskedDyadicMajorant_nonneg (k : ℝ) (D : Set Position) (z : Position × Position) :
    0 ≤ maskedDyadicMajorant k D z := by
  unfold maskedDyadicMajorant
  split_ifs <;> positivity

theorem maskedDyadicKernel_norm_le {k : ℝ} (hk : 0 ≤ k) (D : Set Position)
    (z : Position × Position) : ‖maskedDyadicKernel k D z‖ ≤ maskedDyadicMajorant k D z := by
  unfold maskedDyadicKernel maskedDyadicMajorant
  split_ifs
  · simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using
      dyadicRemainder_sharp_norm_le hk (z.1 - z.2)
  · simp

theorem maskedDyadicMajorant_swap (k : ℝ) (D : Set Position) (x y : Position) :
    maskedDyadicMajorant k D (y, x) = maskedDyadicMajorant k D (x, y) := by
  simp [maskedDyadicMajorant, and_comm, norm_sub_rev]

theorem maskedDyadicMajorant_row_integrable (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (x : Position) : Integrable (fun y => maskedDyadicMajorant k D (x, y)) volume := by
  by_cases hx : x ∈ D
  · have hin : IntegrableOn (fun y : Position =>
        (3 * k ^ 2 / (8 * Real.pi)) * ‖y - x‖⁻¹) D volume :=
      (newton_bounded_support_integrable D hsub x).const_mul (3 * k ^ 2 / (8 * Real.pi))
    have h := hin.integrable_indicator hD
    convert h using 1
    funext y
    simp [maskedDyadicMajorant, hx, indicator, norm_sub_rev]
  · simp [maskedDyadicMajorant, hx]

theorem maskedDyadicMajorant_row_bound (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (hvol : volume.real D = 4 * Real.pi / 3 * a ^ 3) (x : Position) :
    (∫ y, maskedDyadicMajorant k D (x, y)) ≤ 3 / 4 * k ^ 2 * a ^ 2 := by
  by_cases hx : x ∈ D
  · have hfun : (fun y => maskedDyadicMajorant k D (x, y)) =
        D.indicator (fun y => (3 * k ^ 2 / (8 * Real.pi)) * ‖x - y‖⁻¹) := by
      funext y
      simp [maskedDyadicMajorant, hx, indicator]
    rw [hfun, integral_indicator hD, integral_const_mul]
    apply (mul_le_mul_of_nonneg_left
      (newton_bounded_support_uniform D hD hR ha hsub hvol x) (by positivity)).trans_eq
    field_simp
    ring
  · simp [maskedDyadicMajorant, hx]
    positivity

theorem setSupported_le_ball (D : Set Position) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    setSupportedL2 (E := Vector) volume D ≤ supportedVectorL2 R := by
  intro f hf
  change ∀ᵐ x ∂volume, x ∉ D → f x = 0 at hf
  change ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Position) R → f x = 0
  filter_upwards [hf] with x hx
  intro hxb
  exact hx (fun hxd => hxb (hsub hxd))

def setToBallCLM (D : Set Position) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    SetSupportedL2 (E := Vector) volume D →L[ℂ] SupportedVectorL2 R :=
  (Submodule.inclusion (setSupported_le_ball D hsub)).mkContinuous 1 fun f => by
    change ‖(f : VectorL2)‖ ≤ 1 * ‖(f : VectorL2)‖
    simp

def supportInputCLM (D : Set Position) (hD : MeasurableSet D) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) : VectorL2 →L[ℂ] SupportedVectorL2 R :=
  setToBallCLM D hsub ∘L setRestrictionCLM volume D hD

def maskedRemainderOperator (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    VectorL2 →L[ℂ] VectorL2 :=
  (setSupportedL2 (E := Vector) volume D).subtypeL ∘L setRestrictionCLM volume D hD ∘L
    (supportedVectorL2 R).subtypeL ∘L compactRemainderOperator k R hR ∘L
      supportInputCLM D hD hsub

theorem supportInputCLM_coe (D : Set Position) (hD : MeasurableSet D) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    (supportInputCLM D hD hsub f : VectorL2) =ᵐ[volume] D.indicator (fun x => f x) :=
  indicatorL2_coe volume D hD f

/-- Explicit full-space physical identification for the actual D-masked input
current. It includes the Newton contact term and makes no assumption about a
material equation or smooth tests supported inside D. -/
theorem supportCurrent_outgoing_distribution (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) (i : Fin 3) :
    outgoingVolumeDistribution k
      (supportedPolarization R hR (supportInputCLM D hD hsub f)) i =
      vectorL2ComponentDistribution
        (staticFourierOperator (supportInputCLM D hD hsub f : VectorL2)) i +
        remainderPotentialComponentDistribution k
          (supportedPolarization R hR (supportInputCLM D hD hsub f)) i := by
  rw [outgoingVolumeDistribution_eq_staticFourier_add_remainder,
    supportedPolarization_toLp]

theorem maskedRemainderOperator_coe (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    maskedRemainderOperator k D hD hR hsub f =ᵐ[volume]
      D.indicator (remainderPotential k (supportedPolarization R hR (supportInputCLM D hD hsub f))) := by
  let p := supportInputCLM D hD hsub f
  filter_upwards [indicatorL2_coe volume D hD
      (compactRemainderLp k R hR p), compactRemainderLp_coe k R hR p] with x hx hy
  change indicatorL2 volume D hD (compactRemainderLp k R hR p) x = _
  rw [hx]
  by_cases hxd : x ∈ D
  · have hxb := hsub hxd
    simp only [indicator_of_mem hxd, compactRemainderField, indicator_of_mem hxb] at hy ⊢
    exact hy
  · simp [hxd]

theorem maskedPotential_integral (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (f : VectorL2) (x : Position) :
    D.indicator (remainderPotential k
      (supportedPolarization R hR (supportInputCLM D hD hsub f))) x =
      ∫ y, maskedDyadicKernel k D (x, y) (f y) := by
  let p := supportedPolarization R hR (supportInputCLM D hD hsub f)
  have hcurrent : p.current =ᵐ[volume] D.indicator (fun y => f y) :=
    (supportedPolarization_current_ae R hR _).trans (supportInputCLM_coe D hD hsub f)
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]
    change (∫ y, dyadicRemainder k (x - y) (p.current y)) = _
    apply integral_congr_ae
    filter_upwards [hcurrent] with y hy
    rw [hy]
    by_cases hyd : y ∈ D <;> simp [maskedDyadicKernel, hx, hyd]
  · simp [hx, maskedDyadicKernel]

theorem maskedKernel_vector_row_integrable (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (f : VectorL2) (x : Position) :
    Integrable (fun y => maskedDyadicKernel k D (x, y) (f y)) volume := by
  let p := supportedPolarization R hR (supportInputCLM D hD hsub f)
  have hcurrent : p.current =ᵐ[volume] D.indicator (fun y => f y) :=
    (supportedPolarization_current_ae R hR _).trans (supportInputCLM_coe D hD hsub f)
  by_cases hx : x ∈ D
  · apply (remainderPotential_integrable k p x).congr
    filter_upwards [hcurrent] with y hy
    rw [hy]
    by_cases hyd : y ∈ D <;> simp [maskedDyadicKernel, hx, hyd]
  · simp [maskedDyadicKernel, hx]

theorem maskedRemainderOperator_pairing {k : ℝ} (hk : 0 ≤ k)
    (D : Set Position) (hD : MeasurableSet D) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (hvol : volume.real D = 4 * Real.pi / 3 * a ^ 3) (f g : VectorL2) :
    inner ℂ g (maskedRemainderOperator k D hD hR hsub f) =
      ∫ z : Position × Position, inner ℂ (g z.1) (maskedDyadicKernel k D z (f z.2)) := by
  have hcol (y : Position) : Integrable (fun x => maskedDyadicMajorant k D (x, y)) volume := by
    simpa only [maskedDyadicMajorant_swap] using maskedDyadicMajorant_row_integrable k D hD hsub y
  have hcolC (y : Position) : (∫ x, maskedDyadicMajorant k D (x, y)) ≤ 3 / 4 * k ^ 2 * a ^ 2 := by
    simpa only [maskedDyadicMajorant_swap] using maskedDyadicMajorant_row_bound k D hD hR ha hsub hvol y
  have hjoint := kernel_pairing_integrable volume (maskedDyadicKernel k D)
    (maskedDyadicKernel_measurable k D hD).aestronglyMeasurable
    (maskedDyadicMajorant k D) (maskedDyadicMajorant_measurable k D hD).aestronglyMeasurable
    (maskedDyadicMajorant_nonneg k D) (maskedDyadicKernel_norm_le hk D)
    (by positivity : 0 ≤ 3 / 4 * k ^ 2 * a ^ 2)
    (maskedDyadicMajorant_row_integrable k D hD hsub)
    (maskedDyadicMajorant_row_bound k D hD hR ha hsub hvol) hcol hcolC f g
  rw [L2.inner_def]
  calc
    _ = ∫ x, inner ℂ (g x) (∫ y, maskedDyadicKernel k D (x, y) (f y)) := by
      apply integral_congr_ae
      filter_upwards [maskedRemainderOperator_coe k D hD hR hsub f] with x hx
      rw [hx, maskedPotential_integral k D hD hR hsub f x]
    _ = ∫ x, ∫ y, inner ℂ (g x) (maskedDyadicKernel k D (x, y) (f y)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x =>
        ((innerSL ℂ (g x)).integral_comp_comm
          (maskedKernel_vector_row_integrable k D hD hR hsub f x)).symm
    _ = _ := (integral_prod _ hjoint).symm

/-- The paper's sharp `3k²a²/4` bound for the actual outgoing-minus-static
convolution on every measurable bounded support. -/
theorem maskedRemainderOperator_norm_le {k : ℝ} (hk : 0 ≤ k)
    (D : Set Position) (hD : MeasurableSet D) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (hvol : volume.real D = 4 * Real.pi / 3 * a ^ 3) :
    ‖maskedRemainderOperator k D hD hR hsub‖ ≤ 3 / 4 * k ^ 2 * a ^ 2 := by
  apply integral_operator_schur volume (maskedRemainderOperator k D hD hR hsub)
    (maskedDyadicKernel k D) (maskedDyadicKernel_measurable k D hD).aestronglyMeasurable
    (maskedDyadicMajorant k D) (maskedDyadicMajorant_measurable k D hD).aestronglyMeasurable
    (maskedDyadicMajorant_nonneg k D) (maskedDyadicKernel_norm_le hk D)
    (by positivity : 0 ≤ 3 / 4 * k ^ 2 * a ^ 2)
    (maskedDyadicMajorant_row_integrable k D hD hsub)
    (maskedDyadicMajorant_row_bound k D hD hR ha hsub hvol)
  · intro y
    simpa only [maskedDyadicMajorant_swap] using maskedDyadicMajorant_row_integrable k D hD hsub y
  · intro y
    simpa only [maskedDyadicMajorant_swap] using maskedDyadicMajorant_row_bound k D hD hR ha hsub hvol y
  · exact maskedRemainderOperator_pairing hk D hD hR ha hsub hvol

def supportRestrictionCLM (D : Set Position) (hD : MeasurableSet D) : VectorL2 →L[ℂ] VectorL2 :=
  (setSupportedL2 (E := Vector) volume D).subtypeL ∘L setRestrictionCLM volume D hD

theorem supportRestrictionCLM_norm_le (D : Set Position) (hD : MeasurableSet D) :
    ‖supportRestrictionCLM D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖indicatorL2 volume D hD f‖ ≤ 1 * ‖f‖
  simpa using indicatorL2_norm_le volume D hD f

theorem supportRestrictionCLM_apply_norm_le (D : Set Position) (hD : MeasurableSet D)
    (f : VectorL2) : ‖supportRestrictionCLM D hD f‖ ≤ ‖f‖ :=
  indicatorL2_norm_le volume D hD f

def maskedStaticOperator (D : Set Position) (hD : MeasurableSet D) : VectorL2 →L[ℂ] VectorL2 :=
  supportRestrictionCLM D hD ∘L staticFourierOperator ∘L supportRestrictionCLM D hD

theorem maskedStaticOperator_norm_le (D : Set Position) (hD : MeasurableSet D) :
    ‖maskedStaticOperator D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖supportRestrictionCLM D hD (staticFourierOperator (supportRestrictionCLM D hD f))‖ ≤ 1 * ‖f‖
  calc
    _ ≤ ‖staticFourierOperator (supportRestrictionCLM D hD f)‖ := supportRestrictionCLM_apply_norm_le _ _ _
    _ ≤ ‖supportRestrictionCLM D hD f‖ := staticFourierOperator_apply_norm_le _
    _ ≤ ‖f‖ := supportRestrictionCLM_apply_norm_le _ _ _
    _ = _ := by ring

def maskedOutgoingOperator (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    VectorL2 →L[ℂ] VectorL2 :=
  maskedStaticOperator D hD + maskedRemainderOperator k D hD hR hsub

theorem maskedOutgoingOperator_difference_norm_le {k : ℝ} (hk : 0 ≤ k)
    (D : Set Position) (hD : MeasurableSet D) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R)
    (hvol : volume.real D = 4 * Real.pi / 3 * a ^ 3) :
    ‖maskedOutgoingOperator k D hD hR hsub - maskedStaticOperator D hD‖ ≤
      3 / 4 * k ^ 2 * a ^ 2 := by
  unfold maskedOutgoingOperator
  rw [add_sub_cancel_left]
  exact maskedRemainderOperator_norm_le hk D hD hR ha hsub hvol

theorem maskedOutgoingOperator_difference_norm_le_volume {k : ℝ} (hk : 0 ≤ k)
    (D : Set Position) (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (hV : 0 < volume.real D) :
    ‖maskedOutgoingOperator k D hD hR hsub - maskedStaticOperator D hD‖ ≤
      3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2 :=
  maskedOutgoingOperator_difference_norm_le hk D hD hR (volumeRadius_pos hV) hsub
    (volumeRadius_volume hV.le).symm

end QuarticMaxwell
