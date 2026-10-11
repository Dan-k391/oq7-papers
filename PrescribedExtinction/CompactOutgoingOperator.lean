import PrescribedExtinction.NewtonStaticIdentification
import PrescribedExtinction.RemainderCurrentPairing
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! A bounded outgoing-volume operator on the actual vector L² currents
supported in a fixed compact ball. The remainder is the existing genuine
convolution, and the static term is the physically identified Newton operator.
This module constructs their bounded sum, with zero extension of the current
and restriction of the field to the same ball. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped ENNReal

local instance compactOutgoing_operatorNormedAddCommGroup :
    NormedAddCommGroup (Vector →L[ℂ] Vector) := inferInstance
local instance compactOutgoing_operatorNormedSpace :
    NormedSpace ℂ (Vector →L[ℂ] Vector) := inferInstance
local instance compactOutgoing_evaluationNormedAddCommGroup :
    NormedAddCommGroup ((Vector →L[ℂ] Vector) →L[ℂ] Vector) := inferInstance
local instance compactOutgoing_evaluationNormedSpace :
    NormedSpace ℂ ((Vector →L[ℂ] Vector) →L[ℂ] Vector) := inferInstance

/-- The support condition is an a.e. property of the actual L² current. -/
def supportedVectorL2 (R : ℝ) : Submodule ℂ VectorL2 where
  carrier := {f | ∀ᵐ x ∂volume, x ∉ Metric.closedBall 0 R → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := Vector) (p := 2) (μ := volume)] with x hx
    exact fun _ => hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx hx
    intro hxs
    rw [hx]
    change f x + g x = 0
    rw [hfx hxs, hgx hxs, add_zero]
  smul_mem' := by
    intro z f hf
    filter_upwards [hf, Lp.coeFn_smul z f] with x hfx hx
    intro hxs
    rw [hx]
    change z • f x = 0
    rw [hfx hxs, smul_zero]

abbrev SupportedVectorL2 (R : ℝ) := supportedVectorL2 R

theorem supportedVectorL2_current_ae (R : ℝ) (f : SupportedVectorL2 R) :
    (Metric.closedBall 0 R).indicator (fun x : Position => (f : VectorL2) x)
      =ᵐ[volume] (fun x : Position => (f : VectorL2) x) := by
  filter_upwards [f.property] with x hx
  by_cases hxs : x ∈ Metric.closedBall 0 R
  · simp [hxs]
  · simp [hxs, hx hxs]

/-- A pointwise zero extension of an a.e.-supported L² representative. -/
def supportedPolarization (R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    CompactPolarization where
  current := (Metric.closedBall 0 R).indicator (fun x : Position => (f : VectorL2) x)
  radius := R
  radius_nonneg := hR
  memLp := (Lp.memLp (f : VectorL2)).indicator Metric.isClosed_closedBall.measurableSet
  vanish x hx := by
    have hxs : x ∉ Metric.closedBall 0 R := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    exact indicator_of_notMem hxs _

theorem supportedPolarization_current_ae (R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) :
    (supportedPolarization R hR f).current =ᵐ[volume] (f : VectorL2) :=
  supportedVectorL2_current_ae R f

theorem supportedPolarization_toLp (R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    (supportedPolarization R hR f).memLp.toLp (supportedPolarization R hR f).current =
      (f : VectorL2) := by
  apply Lp.ext
  exact (supportedPolarization R hR f).memLp.coeFn_toLp.trans
    (supportedPolarization_current_ae R hR f)

theorem supportedPolarization_current_eLpNorm (R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) :
    (eLpNorm (supportedPolarization R hR f).current 2 volume).toReal = ‖f‖ := by
  rw [eLpNorm_congr_ae (supportedPolarization_current_ae R hR f)]
  exact (Lp.norm_def (f : VectorL2)).symm

def compactRestrictionLp (R : ℝ) (f : VectorL2) : VectorL2 :=
  ((Lp.memLp f).indicator Metric.isClosed_closedBall.measurableSet).toLp
    ((Metric.closedBall 0 R).indicator (fun x => f x))

theorem compactRestrictionLp_coe (R : ℝ) (f : VectorL2) :
    compactRestrictionLp R f =ᵐ[volume] (Metric.closedBall 0 R).indicator (fun x => f x) :=
  ((Lp.memLp f).indicator Metric.isClosed_closedBall.measurableSet).coeFn_toLp

theorem compactRestrictionLp_supported (R : ℝ) (f : VectorL2) :
    compactRestrictionLp R f ∈ supportedVectorL2 R := by
  filter_upwards [compactRestrictionLp_coe R f] with x hx
  intro hxs
  rw [hx, indicator_of_notMem hxs]

theorem compactRestrictionLp_norm_le (R : ℝ) (f : VectorL2) :
    ‖compactRestrictionLp R f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [compactRestrictionLp_coe R f] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _

theorem compactRestrictionLp_add (R : ℝ) (f g : VectorL2) :
    compactRestrictionLp R (f + g) = compactRestrictionLp R f + compactRestrictionLp R g := by
  apply Lp.ext
  filter_upwards [compactRestrictionLp_coe R (f + g), compactRestrictionLp_coe R f,
    compactRestrictionLp_coe R g, Lp.coeFn_add f g,
    Lp.coeFn_add (compactRestrictionLp R f) (compactRestrictionLp R g)] with x hfg hf hg ha hb
  rw [hfg, hb]
  change (Metric.closedBall 0 R).indicator (fun y => (f + g) y) x =
    compactRestrictionLp R f x + compactRestrictionLp R g x
  rw [hf, hg]
  by_cases hx : x ∈ Metric.closedBall 0 R
  · simpa only [indicator_of_mem hx, Pi.add_apply] using ha
  · simp only [indicator_of_notMem hx, add_zero]

theorem compactRestrictionLp_smul (R : ℝ) (z : ℂ) (f : VectorL2) :
    compactRestrictionLp R (z • f) = z • compactRestrictionLp R f := by
  apply Lp.ext
  filter_upwards [compactRestrictionLp_coe R (z • f), compactRestrictionLp_coe R f,
    Lp.coeFn_smul z f, Lp.coeFn_smul z (compactRestrictionLp R f)] with x hzf hf ha hb
  rw [hzf, hb]
  change (Metric.closedBall 0 R).indicator (fun y => (z • f) y) x = z • compactRestrictionLp R f x
  rw [hf]
  by_cases hx : x ∈ Metric.closedBall 0 R
  · simpa only [indicator_of_mem hx, Pi.smul_apply] using ha
  · simp only [indicator_of_notMem hx, smul_zero]

def compactRestrictionLinear (R : ℝ) : VectorL2 →ₗ[ℂ] SupportedVectorL2 R where
  toFun f := ⟨compactRestrictionLp R f, compactRestrictionLp_supported R f⟩
  map_add' f g := Subtype.ext (compactRestrictionLp_add R f g)
  map_smul' z f := Subtype.ext (compactRestrictionLp_smul R z f)

def compactRestrictionCLM (R : ℝ) : VectorL2 →L[ℂ] SupportedVectorL2 R :=
  (compactRestrictionLinear R).mkContinuous 1 fun f => by
    change ‖compactRestrictionLp R f‖ ≤ 1 * ‖f‖
    simpa using compactRestrictionLp_norm_le R f

theorem compactRestrictionCLM_norm_le (R : ℝ) : ‖compactRestrictionCLM R‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem compactRestrictionLp_eq_self_iff_supported (R : ℝ) (f : VectorL2) :
    compactRestrictionLp R f = f ↔ f ∈ supportedVectorL2 R := by
  constructor
  · intro h
    rw [← h]
    exact compactRestrictionLp_supported R f
  · intro hf
    apply Lp.ext
    exact (compactRestrictionLp_coe R f).trans
      (supportedVectorL2_current_ae R ⟨f, hf⟩)

theorem supportedVectorL2_isClosed (R : ℝ) :
    IsClosed (supportedVectorL2 R : Set VectorL2) := by
  have he : (supportedVectorL2 R : Set VectorL2) =
      {f : VectorL2 | (supportedVectorL2 R).subtypeL (compactRestrictionCLM R f) = f} := by
    ext f
    change f ∈ supportedVectorL2 R ↔ compactRestrictionLp R f = f
    exact (compactRestrictionLp_eq_self_iff_supported R f).symm
  rw [he]
  exact isClosed_eq
    ((supportedVectorL2 R).subtypeL.continuous.comp (compactRestrictionCLM R).continuous)
    continuous_id

instance supportedVectorL2_completeSpace (R : ℝ) : CompleteSpace (SupportedVectorL2 R) := by
  let : IsClosed (supportedVectorL2 R : Set VectorL2) := supportedVectorL2_isClosed R
  exact inferInstance

def compactStaticOperator (R : ℝ) : SupportedVectorL2 R →L[ℂ] SupportedVectorL2 R :=
  compactRestrictionCLM R ∘L staticFourierOperator ∘L (supportedVectorL2 R).subtypeL

theorem compactStaticOperator_apply_norm_le (R : ℝ) (f : SupportedVectorL2 R) :
    ‖compactStaticOperator R f‖ ≤ ‖f‖ := by
  exact (compactRestrictionLp_norm_le R (staticFourierOperator (f : VectorL2))).trans
    (staticFourierOperator_apply_norm_le (f : VectorL2))

def compactRemainderField (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) : Field :=
  (Metric.closedBall 0 R).indicator (remainderPotential k (supportedPolarization R hR f))

theorem compactRemainderField_memLp (k R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) : MemLp (compactRemainderField k R hR f) 2 volume := by
  rw [compactRemainderField, memLp_indicator_iff_restrict Metric.isClosed_closedBall.measurableSet]
  exact remainderPotential_memLp_on_compact k (supportedPolarization R hR f) _
    (isCompact_closedBall _ _)

def compactRemainderLp (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) : VectorL2 :=
  (compactRemainderField_memLp k R hR f).toLp (compactRemainderField k R hR f)

theorem compactRemainderLp_coe (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    compactRemainderLp k R hR f =ᵐ[volume] compactRemainderField k R hR f :=
  (compactRemainderField_memLp k R hR f).coeFn_toLp

theorem compactRemainderLp_supported (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    compactRemainderLp k R hR f ∈ supportedVectorL2 R := by
  filter_upwards [compactRemainderLp_coe k R hR f] with x hx
  intro hxs
  rw [hx]
  exact indicator_of_notMem hxs _

/-- Explicit finite bound, obtained from the actual truncated kernel L² norm
and the volume of the compact output ball. -/
def compactRemainderConstant (k R : ℝ) : ℝ :=
  ‖vectorOperatorApply‖ * (eLpNorm (cutoffDyadicRemainder k (R + R)) 2 volume).toReal *
    (volume.real (Metric.closedBall (0 : Position) R)) ^ (1 / (2 : ℝ))

theorem compactRemainderConstant_nonneg (k R : ℝ) : 0 ≤ compactRemainderConstant k R := by
  unfold compactRemainderConstant
  positivity

theorem compactRemainderLp_norm_le (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    ‖compactRemainderLp k R hR f‖ ≤ compactRemainderConstant k R * ‖f‖ := by
  let p := supportedPolarization R hR f
  let K : Set Position := Metric.closedBall 0 R
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hb := remainderPotential_eLpNorm_le k p K hK R (fun x hx => by
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)
  have hfin : volume K < ⊤ := (isCompact_closedBall (0 : Position) R).measure_lt_top
  have ht : remainderPotentialBound k p R * volume K ^ (1 / (2 : ℝ)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (remainderPotentialBound_lt_top k p R).ne
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne)
  rw [Lp.norm_def, eLpNorm_congr_ae (compactRemainderLp_coe k R hR f),
    compactRemainderField, eLpNorm_indicator_eq_eLpNorm_restrict hK]
  apply (ENNReal.toReal_mono ht hb).trans_eq
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  unfold remainderPotentialBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm,
    supportedPolarization_current_eLpNorm R hR f]
  change ‖vectorOperatorApply‖ * ‖f‖ *
      (eLpNorm (cutoffDyadicRemainder k (R + R)) 2 volume).toReal *
        (volume K).toReal ^ (1 / (2 : ℝ)) = _
  unfold compactRemainderConstant
  change _ = ‖vectorOperatorApply‖ *
      (eLpNorm (cutoffDyadicRemainder k (R + R)) 2 volume).toReal *
        (volume K).toReal ^ (1 / (2 : ℝ)) * ‖f‖
  ring

theorem supportedPolarization_add_current_ae (R : ℝ) (hR : 0 ≤ R)
    (f g : SupportedVectorL2 R) :
    (supportedPolarization R hR (f + g)).current =ᵐ[volume]
      ((supportedPolarization R hR f).add (supportedPolarization R hR g)).current := by
  filter_upwards [Lp.coeFn_add (f : VectorL2) (g : VectorL2)] with x hx
  change (Metric.closedBall 0 R).indicator (fun y => ((f : VectorL2) + (g : VectorL2)) y) x =
    ((Metric.closedBall 0 R).indicator (fun y => (f : VectorL2) y) +
      (Metric.closedBall 0 R).indicator (fun y => (g : VectorL2) y)) x
  by_cases hxs : x ∈ Metric.closedBall 0 R
  · simpa only [indicator_of_mem hxs, Pi.add_apply] using hx
  · simp only [indicator_of_notMem hxs, Pi.add_apply, add_zero]

theorem supportedPolarization_smul_current_ae (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (f : SupportedVectorL2 R) :
    (supportedPolarization R hR (z • f)).current =ᵐ[volume]
      ((supportedPolarization R hR f).scale z).current := by
  filter_upwards [Lp.coeFn_smul z (f : VectorL2)] with x hx
  change (Metric.closedBall 0 R).indicator (fun y => (z • (f : VectorL2)) y) x =
    z • (Metric.closedBall 0 R).indicator (fun y => (f : VectorL2) y) x
  by_cases hxs : x ∈ Metric.closedBall 0 R
  · simpa only [indicator_of_mem hxs, Pi.smul_apply] using hx
  · simp only [indicator_of_notMem hxs, smul_zero]

theorem compactRemainderLp_add (k R : ℝ) (hR : 0 ≤ R) (f g : SupportedVectorL2 R) :
    compactRemainderLp k R hR (f + g) = compactRemainderLp k R hR f + compactRemainderLp k R hR g := by
  have hp := remainderPotential_congr_current k _ _ (supportedPolarization_add_current_ae R hR f g)
  rw [remainderPotential_add] at hp
  apply Lp.ext
  filter_upwards [compactRemainderLp_coe k R hR (f + g), compactRemainderLp_coe k R hR f,
    compactRemainderLp_coe k R hR g,
    Lp.coeFn_add (compactRemainderLp k R hR f) (compactRemainderLp k R hR g)] with x hfg hf hg ha
  rw [hfg, ha]
  change compactRemainderField k R hR (f + g) x =
    compactRemainderLp k R hR f x + compactRemainderLp k R hR g x
  rw [hf, hg]
  change (Metric.closedBall 0 R).indicator (remainderPotential k (supportedPolarization R hR (f + g))) x = _
  rw [hp]
  exact congrFun (indicator_add _ _ _) x

theorem compactRemainderLp_smul (k R : ℝ) (hR : 0 ≤ R) (z : ℂ) (f : SupportedVectorL2 R) :
    compactRemainderLp k R hR (z • f) = z • compactRemainderLp k R hR f := by
  have hp := remainderPotential_congr_current k _ _ (supportedPolarization_smul_current_ae R hR z f)
  rw [remainderPotential_smul] at hp
  apply Lp.ext
  filter_upwards [compactRemainderLp_coe k R hR (z • f), compactRemainderLp_coe k R hR f,
    Lp.coeFn_smul z (compactRemainderLp k R hR f)] with x hzf hf ha
  rw [hzf, ha]
  change compactRemainderField k R hR (z • f) x = z • compactRemainderLp k R hR f x
  rw [hf]
  change (Metric.closedBall 0 R).indicator (remainderPotential k (supportedPolarization R hR (z • f))) x = _
  rw [hp]
  by_cases hx : x ∈ Metric.closedBall 0 R
  · simp only [compactRemainderField, indicator_of_mem hx, Pi.smul_apply]
  · simp only [compactRemainderField, indicator_of_notMem hx, smul_zero]

def compactRemainderLinear (k R : ℝ) (hR : 0 ≤ R) :
    SupportedVectorL2 R →ₗ[ℂ] SupportedVectorL2 R where
  toFun f := ⟨compactRemainderLp k R hR f, compactRemainderLp_supported k R hR f⟩
  map_add' f g := Subtype.ext (compactRemainderLp_add k R hR f g)
  map_smul' z f := Subtype.ext (compactRemainderLp_smul k R hR z f)

def compactRemainderOperator (k R : ℝ) (hR : 0 ≤ R) :
    SupportedVectorL2 R →L[ℂ] SupportedVectorL2 R :=
  (compactRemainderLinear k R hR).mkContinuous (compactRemainderConstant k R)
    (compactRemainderLp_norm_le k R hR)

theorem compactRemainderOperator_norm_le (k R : ℝ) (hR : 0 ≤ R) :
    ‖compactRemainderOperator k R hR‖ ≤ compactRemainderConstant k R :=
  LinearMap.mkContinuous_norm_le _ (compactRemainderConstant_nonneg k R) _

/-- The genuine Newton static operator plus outgoing-minus-static convolution,
restricted to the compact ball. Distributional identification is stated in the
Green-current bridge, rather than assumed in this operator's type. -/
def compactOutgoingOperator (k R : ℝ) (hR : 0 ≤ R) :
    SupportedVectorL2 R →L[ℂ] SupportedVectorL2 R :=
  compactStaticOperator R + compactRemainderOperator k R hR

theorem compactOutgoingOperator_apply_norm_le (k R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) :
    ‖compactOutgoingOperator k R hR f‖ ≤ (1 + compactRemainderConstant k R) * ‖f‖ := by
  calc
    _ ≤ ‖compactStaticOperator R f‖ + ‖compactRemainderOperator k R hR f‖ := norm_add_le _ _
    _ ≤ ‖f‖ + compactRemainderConstant k R * ‖f‖ :=
      add_le_add (compactStaticOperator_apply_norm_le R f) (compactRemainderLp_norm_le k R hR f)
    _ = _ := by ring

theorem compactOutgoingOperator_norm_le (k R : ℝ) (hR : 0 ≤ R) :
    ‖compactOutgoingOperator k R hR‖ ≤ 1 + compactRemainderConstant k R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [compactRemainderConstant_nonneg k R])
  exact compactOutgoingOperator_apply_norm_le k R hR

theorem compactOutgoingOperator_coe (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    (compactOutgoingOperator k R hR f : VectorL2) =ᵐ[volume]
      (Metric.closedBall 0 R).indicator (fun x : Position =>
        (staticFourierOperator (f : VectorL2)) x +
          remainderPotential k (supportedPolarization R hR f) x) := by
  filter_upwards [Lp.coeFn_add
      (compactRestrictionLp R (staticFourierOperator (f : VectorL2))) (compactRemainderLp k R hR f),
    compactRestrictionLp_coe R (staticFourierOperator (f : VectorL2)),
    compactRemainderLp_coe k R hR f] with x ha hs hr
  change (compactRestrictionLp R (staticFourierOperator (f : VectorL2)) + compactRemainderLp k R hR f) x = _
  rw [ha]
  change compactRestrictionLp R (staticFourierOperator (f : VectorL2)) x +
    compactRemainderLp k R hR f x = _
  rw [hs, hr]
  exact (congrFun (indicator_add _ _ _) x).symm

end OQ7Prescribed
