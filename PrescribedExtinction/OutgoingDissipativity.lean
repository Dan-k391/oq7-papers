import PrescribedExtinction.SmoothOutgoingDissipativity
import PrescribedExtinction.CompactCurrentDensity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def CompactPolarization.toSupportedLp (p : CompactPolarization) (R : ℝ) (hpR : p.radius ≤ R) :
    SupportedVectorL2 R := ⟨p.memLp.toLp p.current, by
  filter_upwards [p.memLp.coeFn_toLp] with x hx
  intro hxs
  rw [hx]
  apply p.vanish
  have hn : R < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxs
  exact hpR.trans_lt hn⟩

theorem electricVolumeField_congr_current (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : electricVolumeField k p = electricVolumeField k q := by
  have he : p.memLp.toLp p.current = q.memLp.toLp q.current :=
    Lp.ext (p.memLp.coeFn_toLp.trans (h.trans q.memLp.coeFn_toLp.symm))
  funext x
  simp only [electricVolumeField, he, remainderPotential_congr_current k p q h]

theorem compactCurrent_outgoingOperator_coe (k R : ℝ) (hR : 0 ≤ R)
    (p : CompactPolarization) (hpR : p.radius ≤ R) :
    (compactOutgoingOperator k R hR (p.toSupportedLp R hpR) : VectorL2) =ᵐ[volume]
      (Metric.closedBall 0 R).indicator (electricVolumeField k p) := by
  have hcur : (supportedPolarization R hR (p.toSupportedLp R hpR)).current =ᵐ[volume] p.current :=
    (supportedPolarization_current_ae R hR _).trans p.memLp.coeFn_toLp
  have hr := remainderPotential_congr_current k _ p hcur
  filter_upwards [compactOutgoingOperator_coe k R hR (p.toSupportedLp R hpR)] with x hx
  rw [hx]
  change (Metric.closedBall 0 R).indicator (fun x =>
    (staticFourierOperator (p.memLp.toLp p.current)) x +
      remainderPotential k (supportedPolarization R hR (p.toSupportedLp R hpR)) x) x = _
  rw [hr]
  rfl

theorem compactCurrent_outgoingOperator_inner (k R : ℝ) (hR : 0 ≤ R)
    (p : CompactPolarization) (hpR : p.radius ≤ R) :
    inner ℂ (p.toSupportedLp R hpR) (compactOutgoingOperator k R hR (p.toSupportedLp R hpR)) =
      ∫ x : Position, pairing (p.current x) (electricVolumeField k p x) := by
  change inner ℂ (p.memLp.toLp p.current)
    (compactOutgoingOperator k R hR (p.toSupportedLp R hpR) : VectorL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [p.memLp.coeFn_toLp, compactCurrent_outgoingOperator_coe k R hR p hpR] with x hp hx
  rw [hp, hx]
  by_cases hxs : x ∈ Metric.closedBall 0 R
  · rw [indicator_of_mem hxs, pairing_eq_inner]
  · rw [indicator_of_notMem hxs, inner_zero_right]
    have hz := p.vanish x (hpR.trans_lt (show R < ‖x‖ from by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxs))
    simp [hz, pairing]

theorem compactCurrent_outgoingOperator_im_nonneg_of_smooth (k : ℝ) (hk : 0 < k)
    (R : ℝ) (hR : 0 ≤ R) (p : CompactPolarization) (hpR : p.radius ≤ R)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    0 ≤ (inner ℂ (p.toSupportedLp R hpR)
      (compactOutgoingOperator k R hR (p.toSupportedLp R hpR))).im := by
  rw [compactCurrent_outgoingOperator_inner]
  have heq : (∫ x : Position, pairing (p.current x) (electricVolumeField k p x)) =
      ∫ x : Position, pairing (p.current x) (smoothElectricSource k p x) := by
    apply integral_congr_ae
    filter_upwards [smoothElectricSource_eq_ae k p hp] with x hx
    rw [hx]
  rw [heq]
  exact smoothPhysicalSource_work_nonneg k hk p hp

theorem compactCurrent_outgoingOperator_im_nonneg (k : ℝ) (hk : 0 < k)
    (p : CompactPolarization) :
    0 ≤ (inner ℂ (p.toSupportedLp (p.radius + 2) (by linarith))
      (compactOutgoingOperator k (p.radius + 2) (by linarith [p.radius_nonneg])
        (p.toSupportedLp (p.radius + 2) (by linarith)))).im := by
  let S := p.radius + 2
  have hS : 0 ≤ S := by dsimp [S]; linarith [p.radius_nonneg]
  have hpS : p.radius ≤ S := by dsimp [S]; linarith
  let x : SupportedVectorL2 S := p.toSupportedLp S hpS
  let Q : SupportedVectorL2 S → ℝ := fun f => (inner ℂ f (compactOutgoingOperator k S hS f)).im
  have hQ : Continuous Q := Complex.imCLM.continuous.comp
    (continuous_id.inner (compactOutgoingOperator k S hS).continuous)
  change 0 ≤ Q x
  by_contra hx
  have hneg : Q x < 0 := lt_of_not_ge hx
  have hU : IsOpen {f : SupportedVectorL2 S | Q f < 0} := isOpen_lt hQ continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hneg
  obtain ⟨q, hqR, hq, hdist⟩ := compactPolarization_smooth_approximation p (δ / 2) (by positivity)
  have hqS : q.radius ≤ S := by dsimp [S]; rw [hqR]
  let y : SupportedVectorL2 S := q.toSupportedLp S hqS
  have hpos : 0 ≤ Q y := compactCurrent_outgoingOperator_im_nonneg_of_smooth k hk S hS q hqS hq
  have hxy : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    change ‖p.memLp.toLp p.current - q.memLp.toLp q.current‖ < δ
    linarith
  exact (hball hxy).not_ge hpos

theorem physicalOutgoingVolume_work_nonneg (k : ℝ) (hk : 0 < k) (p : CompactPolarization) :
    0 ≤ (∫ x : Position, pairing (p.current x) (electricVolumeField k p x)).im := by
  rw [← compactCurrent_outgoingOperator_inner k (p.radius + 2)
    (by linarith [p.radius_nonneg]) p (by linarith)]
  exact compactCurrent_outgoingOperator_im_nonneg k hk p

/-- Dissipativity of the actual bounded outgoing Maxwell volume operator,
for every compact L² current, without a physical assumption or smoothness restriction. -/
theorem compactOutgoingOperator_im_nonneg (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) : 0 ≤ (inner ℂ f (compactOutgoingOperator k R hR f)).im := by
  let p := supportedPolarization R hR f
  have he : p.toSupportedLp R (by rfl) = f := by
    apply Subtype.ext
    exact supportedPolarization_toLp R hR f
  have hi := compactCurrent_outgoingOperator_inner k R hR p (by rfl)
  rw [he] at hi
  rw [hi]
  exact physicalOutgoingVolume_work_nonneg k hk p

end OQ7Prescribed
