import QuarticMaxwell.SupportedOperators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Literal cosine/sine incident inputs and their L² Taylor bounds on the
same arbitrary bounded measurable support as the Maxwell inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
namespace SourceTaylor
open MeasureTheory Set OQ7Prescribed

variable (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤)

include hD hfin in
theorem scalar_memLp (φ : Position → ℝ) (hφ : AEStronglyMeasurable φ volume)
    (C : ℝ) (hb : ∀ᵐ x ∂volume.restrict D, |φ x| ≤ C) (e : Vector) :
    MemLp (D.indicator (fun x => (φ x : ℂ) • e)) 2 volume := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin.lt_top⟩
  rw [memLp_indicator_iff_restrict hD]
  apply MemLp.of_bound
    ((Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hφ).smul_const e).restrict (C * ‖e‖)
  filter_upwards [hb] with x hx
  simpa [norm_smul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right hx (norm_nonneg e)

def scalarSource (φ : Position → ℝ) (hφ : AEStronglyMeasurable φ volume)
    (C : ℝ) (hb : ∀ᵐ x ∂volume.restrict D, |φ x| ≤ C) (e : Vector) : DomainL2 D :=
  ⟨(scalar_memLp D hD hfin φ hφ C hb e).toLp (D.indicator (fun x => (φ x : ℂ) • e)), by
    change ∀ᵐ x ∂volume, x ∉ D →
      ((scalar_memLp D hD hfin φ hφ C hb e).toLp (D.indicator (fun y => (φ y : ℂ) • e))) x = 0
    filter_upwards [(scalar_memLp D hD hfin φ hφ C hb e).coeFn_toLp] with x hx
    intro hd
    rw [hx, indicator_of_notMem hd]⟩

theorem scalarSource_coe (φ : Position → ℝ) (hφ : AEStronglyMeasurable φ volume)
    (C : ℝ) (hb : ∀ᵐ x ∂volume.restrict D, |φ x| ≤ C) (e : Vector) :
    (scalarSource D hD hfin φ hφ C hb e : VectorL2) =ᵐ[volume]
      D.indicator (fun x => (φ x : ℂ) • e) :=
  (scalar_memLp D hD hfin φ hφ C hb e).coeFn_toLp

def constantSource (e : Vector) : DomainL2 D :=
  scalarSource D hD hfin (fun _ => 1) aestronglyMeasurable_const 1 (by simp) e

def cosSource (t : ℝ) (n : UnitSphere) (e : Vector) : DomainL2 D :=
  scalarSource D hD hfin (fun x => Real.cos (t * inner ℝ (n : Position) x))
    (by fun_prop) 1 (ae_of_all _ fun x => Real.abs_cos_le_one _) e

def sinSource (t : ℝ) (n : UnitSphere) (e : Vector) : DomainL2 D :=
  scalarSource D hD hfin (fun x => Real.sin (t * inner ℝ (n : Position) x))
    (by fun_prop) 1 (ae_of_all _ fun x => Real.abs_sin_le_one _) e

theorem direction_bound (n : UnitSphere) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) {x : Position} (hx : x ∈ D) :
    |inner ℝ (n : Position) x| ≤ R := by
  have hn : ‖(n : Position)‖ = 1 := (mem_sphere_zero_iff_norm).mp n.property
  have hb := abs_real_inner_le_norm (n : Position) x
  have hr : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hsub hx
  simpa only [hn, one_mul] using hb.trans (by simpa [hn] using hr)

def momentSource (n : UnitSphere) (e : Vector) (R : ℝ)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) : DomainL2 D :=
  scalarSource D hD hfin (fun x => inner ℝ (n : Position) x)
    (innerSL ℝ (n : Position)).continuous.aestronglyMeasurable R (by
      filter_upwards [ae_restrict_mem hD] with x hx
      exact direction_bound D n hsub hx) e

theorem constantSource_coe (e : Vector) :
    (constantSource D hD hfin e : VectorL2) =ᵐ[volume] D.indicator (fun _ => e) := by
  simpa [constantSource] using scalarSource_coe D hD hfin (fun _ => 1) aestronglyMeasurable_const
    1 (by simp) e

theorem cosSource_coe (t : ℝ) (n : UnitSphere) (e : Vector) :
    (cosSource D hD hfin t n e : VectorL2) =ᵐ[volume]
      D.indicator (fun x => ((Real.cos (t * inner ℝ (n : Position) x) : ℝ) : ℂ) • e) :=
  scalarSource_coe D hD hfin _ _ _ _ _

theorem sinSource_coe (t : ℝ) (n : UnitSphere) (e : Vector) :
    (sinSource D hD hfin t n e : VectorL2) =ᵐ[volume]
      D.indicator (fun x => ((Real.sin (t * inner ℝ (n : Position) x) : ℝ) : ℂ) • e) :=
  scalarSource_coe D hD hfin _ _ _ _ _

theorem momentSource_coe (n : UnitSphere) (e : Vector) (R : ℝ)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    (momentSource D hD hfin n e R hsub : VectorL2) =ᵐ[volume]
      D.indicator (fun x => ((inner ℝ (n : Position) x : ℝ) : ℂ) • e) :=
  scalarSource_coe D hD hfin _ _ _ _ _

theorem norm_comparison (e : Vector) (f : DomainL2 D) (C : ℝ)
    (hb : ∀ᵐ x ∂volume, x ∈ D → ‖(f : VectorL2) x‖ ≤ C * ‖e‖) :
    ‖f‖ ≤ C * ‖constantSource D hD hfin e‖ := by
  change ‖(f : VectorL2)‖ ≤ C * ‖(constantSource D hD hfin e : VectorL2)‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hb, constantSource_coe D hD hfin e, f.property] with x hx hc hf
  rw [hc]
  by_cases hd : x ∈ D
  · rw [indicator_of_mem hd]
    exact hx hd
  · rw [indicator_of_notMem hd, hf hd]
    simp

theorem cos_scalar_remainder (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

theorem cosine_remainder (t : ℝ) (n : UnitSphere) (e : Vector) {R : ℝ} (_hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖cosSource D hD hfin t n e - constantSource D hD hfin e‖ ≤
      (t ^ 2 * R ^ 2 / 2) * ‖constantSource D hD hfin e‖ := by
  apply norm_comparison D hD hfin
  filter_upwards [cosSource_coe D hD hfin t n e, constantSource_coe D hD hfin e,
    Lp.coeFn_sub (cosSource D hD hfin t n e : VectorL2)
      (constantSource D hD hfin e : VectorL2)] with x hc hconst hsubx
  intro hx
  change ‖((cosSource D hD hfin t n e : VectorL2) - (constantSource D hD hfin e : VectorL2)) x‖ ≤ _
  rw [hsubx]
  change ‖(cosSource D hD hfin t n e : VectorL2) x - (constantSource D hD hfin e : VectorL2) x‖ ≤ _
  rw [hc, hconst, indicator_of_mem hx, indicator_of_mem hx]
  have hv : ((Real.cos (t * inner ℝ (n : Position) x) : ℝ) : ℂ) • e - e =
      (((Real.cos (t * inner ℝ (n : Position) x) - 1 : ℝ) : ℂ)) • e := by
    push_cast
    simp [sub_smul]
  rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
  apply (cos_scalar_remainder _).trans
  have ha := direction_bound D n hsub hx
  have hasq : (inner ℝ (n : Position) x) ^ 2 ≤ R ^ 2 := by nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2]
  nlinarith [mul_le_mul_of_nonneg_left hasq (sq_nonneg t)]

theorem sine_remainder (t : ℝ) (n : UnitSphere) (e : Vector) {R : ℝ} (_hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖sinSource D hD hfin t n e - (t : ℂ) • momentSource D hD hfin n e R hsub‖ ≤
      (|t| ^ 3 * R ^ 3 / 6) * ‖constantSource D hD hfin e‖ := by
  apply norm_comparison D hD hfin
  filter_upwards [sinSource_coe D hD hfin t n e, momentSource_coe D hD hfin n e R hsub,
    Lp.coeFn_sub (sinSource D hD hfin t n e : VectorL2)
      ((t : ℂ) • (momentSource D hD hfin n e R hsub : VectorL2)),
    Lp.coeFn_smul (t : ℂ) (momentSource D hD hfin n e R hsub : VectorL2)] with x hs hm hsubx hsmul
  intro hx
  change ‖((sinSource D hD hfin t n e : VectorL2) -
    (t : ℂ) • (momentSource D hD hfin n e R hsub : VectorL2)) x‖ ≤ _
  rw [hsubx]
  change ‖(sinSource D hD hfin t n e : VectorL2) x -
    ((t : ℂ) • (momentSource D hD hfin n e R hsub : VectorL2)) x‖ ≤ _
  rw [hsmul]
  change ‖(sinSource D hD hfin t n e : VectorL2) x -
    (t : ℂ) • (momentSource D hD hfin n e R hsub : VectorL2) x‖ ≤ _
  rw [hs, hm, indicator_of_mem hx, indicator_of_mem hx]
  have hv : ((Real.sin (t * inner ℝ (n : Position) x) : ℝ) : ℂ) • e -
      (t : ℂ) • ((inner ℝ (n : Position) x : ℝ) : ℂ) • e =
      (((Real.sin (t * inner ℝ (n : Position) x) - t * inner ℝ (n : Position) x : ℝ) : ℂ)) • e := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, sub_smul, smul_smul]
  rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
  have hs := Real.abs_sub_sin_le (t * inner ℝ (n : Position) x)
  rw [abs_sub_comm] at hs
  apply hs.trans
  rw [abs_mul, mul_pow]
  gcongr
  exact direction_bound D n hsub hx

theorem moment_norm (n : UnitSphere) (e : Vector) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖momentSource D hD hfin n e R hsub‖ ≤ R * ‖constantSource D hD hfin e‖ := by
  apply norm_comparison D hD hfin
  filter_upwards [momentSource_coe D hD hfin n e R hsub] with x hm
  intro hx
  rw [hm, indicator_of_mem hx, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (direction_bound D n hsub hx) (norm_nonneg e)

theorem sine_norm (t : ℝ) (n : UnitSphere) (e : Vector) {R : ℝ}
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖sinSource D hD hfin t n e‖ ≤ |t| * R * ‖constantSource D hD hfin e‖ := by
  apply norm_comparison D hD hfin
  filter_upwards [sinSource_coe D hD hfin t n e] with x hs
  intro hx
  rw [hs, indicator_of_mem hx, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg e)
  apply (Real.abs_sin_le_abs (x := t * inner ℝ (n : Position) x)).trans
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (direction_bound D n hsub hx) (abs_nonneg t)

theorem cosine_norm (t : ℝ) (n : UnitSphere) (e : Vector) :
    ‖cosSource D hD hfin t n e‖ ≤ ‖constantSource D hD hfin e‖ := by
  have hh : ‖cosSource D hD hfin t n e‖ ≤ 1 * ‖constantSource D hD hfin e‖ := by
    apply norm_comparison D hD hfin
    filter_upwards [cosSource_coe D hD hfin t n e] with x hc
    intro hx
    rw [hc, indicator_of_mem hx, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg e)
  simpa only [one_mul] using hh

theorem phase_cos_sin (t : ℝ) (n : UnitSphere) (x : Position) :
    radiationPhase t n x = ((Real.cos (t * inner ℝ (n : Position) x) : ℝ) : ℂ) -
      Complex.I * ((Real.sin (t * inner ℝ (n : Position) x) : ℝ) : ℂ) := by
  unfold radiationPhase
  rw [show -Complex.I * ((t * inner ℝ (n : Position) x : ℝ) : ℂ) =
    ((-(t * inner ℝ (n : Position) x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

theorem source_decomposition (t : ℝ) (n : UnitSphere) (e : Vector) :
    domainIncidentSource t n e D hD hfin =
      cosSource D hD hfin t n e - Complex.I • sinSource D hD hfin t n e := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [incidentSource_coe t n e D hD hfin, cosSource_coe D hD hfin t n e,
    sinSource_coe D hD hfin t n e,
    Lp.coeFn_sub (cosSource D hD hfin t n e : VectorL2)
      (Complex.I • (sinSource D hD hfin t n e : VectorL2)),
    Lp.coeFn_smul Complex.I (sinSource D hD hfin t n e : VectorL2)] with x hp hc hs hsubx hsmul
  change (incidentSource t n e D hD hfin) x =
    ((cosSource D hD hfin t n e : VectorL2) - Complex.I • (sinSource D hD hfin t n e : VectorL2)) x
  rw [hp, hsubx]
  change D.indicator (incidentWave t n e) x = (cosSource D hD hfin t n e : VectorL2) x -
    (Complex.I • (sinSource D hD hfin t n e : VectorL2)) x
  rw [hsmul]
  change D.indicator (incidentWave t n e) x = (cosSource D hD hfin t n e : VectorL2) x -
    Complex.I • (sinSource D hD hfin t n e : VectorL2) x
  rw [hc, hs]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx, incidentWave, phase_cos_sin, sub_smul, smul_smul]
  · simp [hx]

theorem cosine_neg (t : ℝ) (n : UnitSphere) (e : Vector) :
    cosSource D hD hfin (-t) n e = cosSource D hD hfin t n e := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [cosSource_coe D hD hfin (-t) n e, cosSource_coe D hD hfin t n e] with x hm hp
  rw [hm, hp]
  simp [neg_mul, Real.cos_neg]

theorem sine_neg (t : ℝ) (n : UnitSphere) (e : Vector) :
    sinSource D hD hfin (-t) n e = -sinSource D hD hfin t n e := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sinSource_coe D hD hfin (-t) n e, sinSource_coe D hD hfin t n e,
    Lp.coeFn_neg (sinSource D hD hfin t n e : VectorL2)] with x hm hp hneg
  change (sinSource D hD hfin (-t) n e : VectorL2) x = (-(sinSource D hD hfin t n e : VectorL2)) x
  rw [hm, hneg]
  change D.indicator (fun y => ((Real.sin (-t * inner ℝ (n : Position) y) : ℝ) : ℂ) • e) x =
    -(sinSource D hD hfin t n e : VectorL2) x
  rw [hp]
  by_cases hx : x ∈ D <;> simp [hx, neg_mul, Real.sin_neg]

theorem source_reverse_decomposition (t : ℝ) (n : UnitSphere) (e : Vector) :
    domainIncidentSource (-t) n e D hD hfin =
      cosSource D hD hfin t n e + Complex.I • sinSource D hD hfin t n e := by
  rw [source_decomposition, cosine_neg, sine_neg, smul_neg, sub_neg_eq_add]

theorem constant_eq_source_zero (n : UnitSphere) (e : Vector) :
    constantSource D hD hfin e = domainIncidentSource 0 n e D hD hfin := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [constantSource_coe D hD hfin e, incidentSource_coe 0 n e D hD hfin] with x hc hf
  change (constantSource D hD hfin e : VectorL2) x = (incidentSource 0 n e D hD hfin) x
  rw [hc, hf]
  have hz : incidentWave 0 n e = (fun _ => e) := by
    funext y
    simp [incidentWave, radiationPhase]
  rw [hz]

theorem constant_norm_sq (n : UnitSphere) (e : Vector) :
    ‖constantSource D hD hfin e‖ ^ 2 = volume.real D * ‖e‖ ^ 2 := by
  rw [constant_eq_source_zero D hD hfin n e]
  exact domainIncidentSource_norm_sq 0 n e D hD hfin

theorem vectorConjugate_real_smul (a : ℝ) (e : Vector) (he : vectorConjugate e = e) :
    vectorConjugate ((a : ℂ) • e) = (a : ℂ) • e := by
  ext i
  have hi : star (e i) = e i := by
    simpa only [vectorConjugate_apply] using congrArg (fun v : Vector => v i) he
  simp [vectorConjugate_apply, PiLp.smul_apply, hi]

theorem scalarSource_fixed (φ : Position → ℝ) (hφ : AEStronglyMeasurable φ volume)
    (C : ℝ) (hb : ∀ᵐ x ∂volume.restrict D, |φ x| ≤ C) (e : Vector)
    (he : vectorConjugate e = e) :
    domainConjugate D (scalarSource D hD hfin φ hφ C hb e) = scalarSource D hD hfin φ hφ C hb e := by
  apply Subtype.ext
  apply Lp.ext
  let f := scalarSource D hD hfin φ hφ C hb e
  filter_upwards [conjugateL2_coe (f : VectorL2), scalarSource_coe D hD hfin φ hφ C hb e] with x hc hf
  change (conjugateL2 (f : VectorL2)) x = (f : VectorL2) x
  rw [hc, hf]
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]
    exact vectorConjugate_real_smul (φ x) e he
  · rw [indicator_of_notMem hx]
    ext i
    simp [vectorConjugate_apply]

theorem cosine_fixed (t : ℝ) (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) :
    domainConjugate D (cosSource D hD hfin t n e) = cosSource D hD hfin t n e :=
  scalarSource_fixed D hD hfin _ _ _ _ e he

theorem sine_fixed (t : ℝ) (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) :
    domainConjugate D (sinSource D hD hfin t n e) = sinSource D hD hfin t n e :=
  scalarSource_fixed D hD hfin _ _ _ _ e he

end SourceTaylor
end QuarticMaxwell
