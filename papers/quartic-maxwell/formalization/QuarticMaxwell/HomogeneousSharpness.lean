import QuarticMaxwell.HomogeneousBounds
import QuarticMaxwell.HomogeneousUniform

/-! The original every-resource quartic sharpness theorem for the actual
physical admissible-design supremum. All constants precede the illumination
quantifiers; the homogeneous relative sphere size is fixed before shrinking. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.HomogeneousSharpness
open OQ7Prescribed WeakMaterial PhysicalPowers FixedPatternContrast FixedPatternWork
open HomogeneousMoments SharpnessClass MeasureTheory

def lowerConstant (m : ℝ) (hm : 0 < m) : ℝ :=
  coefficientFloor m (chosenRadius m hm) / 2

def cutoff (m : ℝ) (hm : 0 < m) : ℝ := uniformCutoff m (chosenRadius m hm)

theorem lowerConstant_pos (m : ℝ) (hm : 0 < m) : 0 < lowerConstant m hm :=
  div_pos (coefficientFloor_pos hm (chosenRadius_spec m hm).1) (by norm_num)

theorem cutoff_pos (m : ℝ) (hm : 0 < m) : 0 < cutoff m hm :=
  uniformCutoff_pos hm (chosenRadius_spec m hm).1

theorem pattern_admissible (P : Parameters) (M : ℝ) (hM : P.μ ≤ M) :
    Admissible P.μ M 1 P.body := by
  refine ⟨?_, TwoSphereGeometry.medium_reciprocal P.n P.a P.a_pos P.a_small P.material, ?_, ?_, ?_⟩
  · rw [P.body_volume]
    positivity [P.a_pos]
  · rw [P.material_constants.1]
    exact hM
  · rw [P.material_constants.2]
  · change (3 / 5 : ℝ) ≤ 1
    norm_num

theorem pattern_homogeneous (P : Parameters) (x : Position) :
    P.body.susceptibility x = (Complex.I * (P.μ : ℂ)) • ContinuousLinearMap.id ℂ Vector := by
  simp [Parameters.body, TwoSphereGeometry.medium, Parameters.material,
    TwoSupportBounds.homogeneousPair, TwoSupportStatic.susceptibility, SphereResponse.scalarSusceptibility]

theorem sSup_sandwich (m M : ℝ) (hm : 0 < m) (hM : m ≤ M)
    (n : UnitSphere) (e : Position) (he : ‖e‖ = 1) (htr : inner ℝ (n : Position) e = 0)
    (k R : ℝ) (hk : 0 < k) (hR : 0 < R) (hsmall : k * R ≤ cutoff m hm) :
    lowerConstant m hm * (k * R) ^ 4 ≤ sSup (values m M k R n (complexify e)) ∧
      sSup (values m M k R n (complexify e)) ≤ upperConstant m M * (k * R) ^ 4 := by
  let P := chosenParameters n e he htr m hm
  have hB : Admissible m M 1 P.body := pattern_admissible P M hM
  have hd : denominatorFloor P.μ P.a ≤ D0 P.body P.electric := by
    simpa only [denominatorFloor, referenceVolume, P.body_volume] using P.denominator_lower
  have hc : coefficientFloor P.μ P.a ≤ coefficient P.body P.n P.electric :=
    chosen_coefficient_lower n e he htr m hm
  let Bs := PhysicalDilation.medium P.body R hR
  let s := solution Bs k hk n (complexify e) P.electric_transverse
  let q := solution Bs k hk (opposite n) (complexify e) (opposite_transverse n (complexify e) P.electric_transverse)
  have hlow := P.uniform_physical_lower hd hc k R hk hR hsmall s q
  have hv : contrast Bs k n (complexify e) s q ∈ values m M k R n (complexify e) :=
    ⟨Bs, scaled_admissible m M P.body hB R hR, s, q, rfl⟩
  have hsmall1 : k * R ≤ 1 := hsmall.trans (min_le_left _ _)
  have hu := values_upper m M k R hm hM hk hR hsmall1 n (complexify e)
    P.electric_real P.electric_norm P.electric_transverse
  have hb : BddAbove (values m M k R n (complexify e)) :=
    ⟨upperConstant m M * (k * R) ^ 4, hu⟩
  exact ⟨hlow.trans (le_csSup hb hv), csSup_le ⟨_, hv⟩ hu⟩

/-- Original Theorem 1.3 with the full resource-only quantifier order. The
constants are positive, independent of direction, polarization and physical k;
the lower family is the fixed homogeneous unequal-sphere pattern above. -/
theorem theorem13 (m M : ℝ) (hm : 0 < m) (hM : m ≤ M) :
    ∃ c C t0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < t0 ∧
      ∀ (n : UnitSphere) (e : Position), ‖e‖ = 1 → inner ℝ (n : Position) e = 0 →
      ∀ (k R : ℝ), 0 < k → 0 < R → k * R ≤ t0 →
        c * (k * R) ^ 4 ≤ sSup (values m M k R n (complexify e)) ∧
          sSup (values m M k R n (complexify e)) ≤ C * (k * R) ^ 4 := by
  exact ⟨lowerConstant m hm, upperConstant m M, cutoff m hm,
    lowerConstant_pos m hm, upperConstant_pos m M hm hM, cutoff_pos m hm,
    fun n e he htr k R hk hR hsmall => sSup_sandwich m M hm hM n e he htr k R hk hR hsmall⟩

end QuarticMaxwell.HomogeneousSharpness
