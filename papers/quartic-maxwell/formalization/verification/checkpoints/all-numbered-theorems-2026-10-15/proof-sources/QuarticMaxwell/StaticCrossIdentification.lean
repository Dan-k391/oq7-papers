import QuarticMaxwell.StaticOffSupport
import QuarticMaxwell.CrossBlockOperator

/-! Identification of genuine rectangular static Fourier blocks with the
classical Hessian volume kernel on separated supports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.StaticCrossIdentification
open OQ7Prescribed StaticOffSupport MeasureTheory Set

theorem staticFourier_cross_representation (D : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R)
    (f : DomainL2 D) (U : Set OQ7Prescribed.Position) (hU : IsOpen U)
    {d : ℝ} (hd : 0 < d) (hsep : ∀ x ∈ U, ∀ y ∈ D, d ≤ ‖x - y‖) :
    ∀ᵐ x ∂volume, x ∈ U → staticFourierOperator (f : VectorL2) x =
      ∫ y : OQ7Prescribed.Position, StaticHessian.newtonHessianOperator (x - y) ((f : VectorL2) y) := by
  let p := domainPolarization D hD hR hsub f
  have hcur : p.current =ᵐ[volume] (f : VectorL2) := domainPolarization_current_ae D hD hR hsub f
  have hzero : ∀ᵐ y ∂volume, y ∉ D → p.current y = 0 := by
    filter_upwards [hcur, f.property] with y hy hf hmem
    rw [hy, hf hmem]
  have h := staticFourier_vector_separated_ae p D U hU hzero hd hsep
  have hto : p.memLp.toLp p.current = (f : VectorL2) := domainPolarization_toLp D hD hR hsub f
  rw [hto] at h
  filter_upwards [h] with x hx hmem
  rw [hx hmem]
  unfold vectorKernelField
  apply integral_congr_ae
  filter_upwards [hcur, f.property] with y hy hf
  rw [hy]
  by_cases hymem : y ∈ D
  · have hnorm : d / 2 < ‖x - y‖ := lt_of_lt_of_le (by linarith) (hsep x hmem y hymem)
    simp [exteriorHessian, Set.indicator, hnorm]
  · rw [hf hymem]
    simp

end QuarticMaxwell.StaticCrossIdentification


namespace QuarticMaxwell.StaticCrossIdentification
open OQ7Prescribed MeasureTheory Set

def staticCrossBlock (U D : Set OQ7Prescribed.Position) (hU : MeasurableSet U) :
    DomainL2 D →L[ℂ] DomainL2 U :=
  setRestrictionCLM volume U hU ∘L staticFourierOperator ∘L
    (setSupportedL2 (E := Vector) volume D).subtypeL

theorem staticCrossBlock_eq_kernel (U D : Set OQ7Prescribed.Position)
    (hU : IsOpen U) (hD : MeasurableSet D) (hfinU : volume U ≠ ⊤) (hfinD : volume D ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R)
    (d : ℝ) (hd : 0 < d) (hsep : ∀ x ∈ U, ∀ y ∈ D, d ≤ ‖x - y‖) :
    staticCrossBlock U D hU.measurableSet =
      CrossBlockOperator.operator U D hU.measurableSet hD hfinU hfinD d hd hsep := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  have hrepr := staticFourier_cross_representation D hD hR hsub f U hU hd hsep
  have hkernel := CrossBlockOperator.operator_coe_on U D hU.measurableSet hD hfinU hfinD d hd hsep f
  have hzero := (CrossBlockOperator.operator U D hU.measurableSet hD hfinU hfinD d hd hsep f).property
  filter_upwards [indicatorL2_coe volume U hU.measurableSet (staticFourierOperator (f : VectorL2)),
    hrepr, hkernel, hzero] with x hm hs hk hz
  change (indicatorL2 volume U hU.measurableSet (staticFourierOperator (f : VectorL2))) x = _
  rw [hm]
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, hs hx, hk hx]
  · rw [indicator_of_notMem hx, hz hx]

theorem staticCrossBlock_norm_le (U D : Set OQ7Prescribed.Position)
    (hU : IsOpen U) (hD : MeasurableSet D) (hfinU : volume U ≠ ⊤) (hfinD : volume D ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R)
    (d : ℝ) (hd : 0 < d) (hsep : ∀ x ∈ U, ∀ y ∈ D, d ≤ ‖x - y‖) :
    ‖staticCrossBlock U D hU.measurableSet‖ ≤
      Real.sqrt (volume.real U * volume.real D) / (2 * Real.pi * d ^ 3) := by
  rw [staticCrossBlock_eq_kernel U D hU hD hfinU hfinD hR hsub d hd hsep]
  exact CrossBlockOperator.operator_norm_le U D hU.measurableSet hD hfinU hfinD d hd hsep

end QuarticMaxwell.StaticCrossIdentification
