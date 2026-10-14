import PrescribedExtinction.SmoothReciprocity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def vectorConjugateLinear : Vector →ₗ[ℝ] Vector where
  toFun := vectorConjugate
  map_add' u v := by ext i; simp [vectorConjugate_apply, PiLp.add_apply]
  map_smul' r v := by ext i; simp [vectorConjugate_apply, PiLp.smul_apply, Complex.real_smul]

def vectorConjugateCLM : Vector →L[ℝ] Vector :=
  vectorConjugateLinear.mkContinuous 1 (fun v => by
    change ‖vectorConjugate v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using (vectorConjugate_norm v).le)

theorem vectorConjugateCLM_norm_le : ‖vectorConjugateCLM‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

def supportedVectorConjugateLinear (R : ℝ) : SupportedVectorL2 R →ₗ[ℝ] SupportedVectorL2 R where
  toFun f := ⟨vectorConjugateCLM.compLp (f : VectorL2), by
    change ∀ᵐ x ∂volume, x ∉ Metric.closedBall 0 R →
      (vectorConjugateCLM.compLp (f : VectorL2)) x = 0
    filter_upwards [vectorConjugateCLM.coeFn_compLp (f : VectorL2), f.property] with x hx hf
    intro hxs
    rw [hx, hf hxs, map_zero]⟩
  map_add' f g := Subtype.ext (map_add (vectorConjugateCLM.compLpL 2 volume) _ _)
  map_smul' r f := Subtype.ext (map_smul (vectorConjugateCLM.compLpL 2 volume) r _)

def supportedVectorConjugate (R : ℝ) : SupportedVectorL2 R →L[ℝ] SupportedVectorL2 R :=
  (supportedVectorConjugateLinear R).mkContinuous 1 (fun f => by
    apply (vectorConjugateCLM.norm_compLp_le (f : VectorL2)).trans
    exact mul_le_mul_of_nonneg_right vectorConjugateCLM_norm_le (norm_nonneg _))

theorem supportedVectorConjugate_coe (R : ℝ) (f : SupportedVectorL2 R) :
    (supportedVectorConjugate R f : VectorL2) =ᵐ[volume] fun x => vectorConjugate ((f : VectorL2) x) :=
  vectorConjugateCLM.coeFn_compLp _

theorem compactCurrents_outgoingOperator_bilinear (k R : ℝ) (hR : 0 ≤ R)
    (p q : CompactPolarization) (hpR : p.radius ≤ R) (hqR : q.radius ≤ R) :
    inner ℂ (supportedVectorConjugate R (p.toSupportedLp R hpR))
      (compactOutgoingOperator k R hR (q.toSupportedLp R hqR)) =
        ∫ x : Position, bilinear (p.current x) (electricVolumeField k q x) := by
  change inner ℂ (supportedVectorConjugate R (p.toSupportedLp R hpR) : VectorL2)
    (compactOutgoingOperator k R hR (q.toSupportedLp R hqR) : VectorL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [supportedVectorConjugate_coe R (p.toSupportedLp R hpR), p.memLp.coeFn_toLp,
    compactCurrent_outgoingOperator_coe k R hR q hqR] with x hc hp hx
  rw [hc, hx]
  change inner ℂ (vectorConjugate ((p.memLp.toLp p.current) x))
    ((Metric.closedBall 0 R).indicator (electricVolumeField k q) x) = _
  rw [hp, ← bilinear_eq_conjugate_inner]
  by_cases hxs : x ∈ Metric.closedBall 0 R
  · rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs]
    have hz := p.vanish x (hpR.trans_lt (show R < ‖x‖ from by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxs))
    simp [hz, bilinear]

theorem compactCurrents_bilinear_volume_integrable (k : ℝ) (p q : CompactPolarization) :
    Integrable (fun x => bilinear (p.current x) (electricVolumeField k q x)) volume := by
  let R := max p.radius q.radius
  have hR : 0 ≤ R := p.radius_nonneg.trans (le_max_left _ _)
  have hpR : p.radius ≤ R := le_max_left _ _
  have hqR : q.radius ≤ R := le_max_right _ _
  apply (L2.integrable_inner (𝕜 := ℂ)
    (supportedVectorConjugate R (p.toSupportedLp R hpR) : VectorL2)
    (compactOutgoingOperator k R hR (q.toSupportedLp R hqR) : VectorL2)).congr
  filter_upwards [supportedVectorConjugate_coe R (p.toSupportedLp R hpR), p.memLp.coeFn_toLp,
    compactCurrent_outgoingOperator_coe k R hR q hqR] with x hc hp hx
  rw [hc, hx]
  change inner ℂ (vectorConjugate ((p.memLp.toLp p.current) x))
    ((Metric.closedBall 0 R).indicator (electricVolumeField k q) x) = _
  rw [hp, ← bilinear_eq_conjugate_inner]
  by_cases hxs : x ∈ Metric.closedBall 0 R
  · rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs]
    have hz := p.vanish x (hpR.trans_lt (show R < ‖x‖ from by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxs))
    simp [hz, bilinear]

/-- Actual Maxwell volume reciprocity for all original compact vector L²
currents, proved through the outgoing Lorentz identity and smooth density. -/
theorem physicalOutgoingVolume_reciprocity (k : ℝ) (hk : 0 < k) (p q : CompactPolarization) :
    (∫ x : Position, bilinear (p.current x) (electricVolumeField k q x)) =
      ∫ x : Position, bilinear (q.current x) (electricVolumeField k p x) := by
  let R := max p.radius q.radius + 2
  have hR : 0 ≤ R := by dsimp [R]; linarith [le_max_left p.radius q.radius, p.radius_nonneg]
  have hpR : p.radius ≤ R := by dsimp [R]; linarith [le_max_left p.radius q.radius]
  have hqR : q.radius ≤ R := by dsimp [R]; linarith [le_max_right p.radius q.radius]
  let x : SupportedVectorL2 R × SupportedVectorL2 R := (p.toSupportedLp R hpR, q.toSupportedLp R hqR)
  let Q : SupportedVectorL2 R × SupportedVectorL2 R → ℂ := fun f =>
    inner ℂ (supportedVectorConjugate R f.1) (compactOutgoingOperator k R hR f.2) -
      inner ℂ (supportedVectorConjugate R f.2) (compactOutgoingOperator k R hR f.1)
  rw [← compactCurrents_outgoingOperator_bilinear k R hR p q hpR hqR,
    ← compactCurrents_outgoingOperator_bilinear k R hR q p hqR hpR]
  apply sub_eq_zero.mp
  change Q x = 0
  have hQ : Continuous Q :=
    (((supportedVectorConjugate R).continuous.comp continuous_fst).inner
      ((compactOutgoingOperator k R hR).continuous.comp continuous_snd)).sub
      (((supportedVectorConjugate R).continuous.comp continuous_snd).inner
        ((compactOutgoingOperator k R hR).continuous.comp continuous_fst))
  by_contra hx
  have hU : IsOpen {f | Q f ≠ 0} := isOpen_ne_fun hQ continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨p', hp'R, hp', hdp⟩ := compactPolarization_smooth_approximation p (δ / 2) (by positivity)
  obtain ⟨q', hq'R, hq', hdq⟩ := compactPolarization_smooth_approximation q (δ / 2) (by positivity)
  have hpS : p'.radius ≤ R := by rw [hp'R]; dsimp [R]; linarith [le_max_left p.radius q.radius]
  have hqS : q'.radius ≤ R := by rw [hq'R]; dsimp [R]; linarith [le_max_right p.radius q.radius]
  let y : SupportedVectorL2 R × SupportedVectorL2 R := (p'.toSupportedLp R hpS, q'.toSupportedLp R hqS)
  have hy : Q y = 0 := by
    change inner ℂ (supportedVectorConjugate R (p'.toSupportedLp R hpS))
      (compactOutgoingOperator k R hR (q'.toSupportedLp R hqS)) -
        inner ℂ (supportedVectorConjugate R (q'.toSupportedLp R hqS))
          (compactOutgoingOperator k R hR (p'.toSupportedLp R hpS)) = 0
    rw [compactCurrents_outgoingOperator_bilinear, compactCurrents_outgoingOperator_bilinear]
    exact sub_eq_zero.mpr (smoothPhysicalSources_reciprocity k hk p' q' hp' hq')
  have hxy : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_eq_norm, norm_sub_rev]
      change ‖p.memLp.toLp p.current - p'.memLp.toLp p'.current‖ < δ
      linarith
    · rw [dist_eq_norm, norm_sub_rev]
      change ‖q.memLp.toLp q.current - q'.memLp.toLp q'.current‖ < δ
      linarith
  exact hball hxy hy

end OQ7Prescribed
