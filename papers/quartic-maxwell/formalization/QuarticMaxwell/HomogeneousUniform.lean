import QuarticMaxwell.HomogeneousCoefficient
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniform forward-work bounds and an explicit homogeneous sphere witness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed SphereStatic SphereResponse SphereExterior SphereDoubleMean
  BlockSourceMoments BlockInteractionMoments TwoSupportStatic TwoSupportBounds TwoSphereGeometry
  SourceTaylor FixedPatternWork FixedPatternScattering MeasureTheory Set

theorem Parameters.material_constants (P : Parameters) : P.body.M = P.μ ∧ P.body.m = P.μ := by
  change P.material.cap = P.μ ∧ P.material.loss = P.μ
  exact ⟨homogeneous_cap P.μ P.μ_pos, homogeneous_loss P.μ P.μ_pos⟩

theorem Parameters.denominator_lower (P : Parameters) :
    P.μ * volume.real P.body.domain / (1 + P.μ) ^ 2 ≤ D0 P.body P.electric := by
  let B := P.body
  let E := StaticInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss B.M_pos
  let q := E.symm P.f0
  have he : StaticInverse.operator B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss q = P.f0 := by
    rw [← StaticInverse.equiv_apply B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss B.M_pos]
    exact E.apply_symm_apply P.f0
  have hJ := TensorMultiplier.inverse_norm_le volume B.domain B.susceptibility B.measurable_susceptibility
    B.M B.cap B.measurable B.m_pos B.loss
  have hA : ‖StaticInverse.operator B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss‖ ≤ 1 / P.μ + 1 := by
    let J := VolumeInverse.inverseSusceptibility B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss
    have hsub := norm_sub_le J (domainStaticOperator B.domain B.measurable)
    have hbound := add_le_add hJ (domainStaticOperator_norm_le B.domain B.measurable)
    have hm : B.m = P.μ := P.material_constants.2
    exact hsub.trans (hbound.trans_eq (by rw [hm]))
  have hN : ‖P.f0‖ ≤ (1 / P.μ + 1) * ‖q‖ := by
    rw [← he]
    exact ((StaticInverse.operator B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss).le_opNorm q).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hNμ : P.μ * ‖P.f0‖ ≤ (1 + P.μ) * ‖q‖ := by
    have h := mul_le_mul_of_nonneg_left hN P.μ_pos.le
    convert h using 1; field_simp [P.μ_pos.ne']
  have hNsq := (sq_le_sq₀ (by positivity [P.μ_pos]) (by positivity [P.μ_pos])).mpr hNμ
  rw [mul_pow, mul_pow, P.f0_norm, Real.sq_sqrt measureReal_nonneg] at hNsq
  have hc := StaticInverse.negative_coercive B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss B.M_pos q
  rw [he] at hc
  have hi := inner_im_symm (𝕜 := ℂ) q P.f0
  change (inner ℂ q P.f0).im = -(inner ℂ P.f0 q).im at hi
  rw [hi, neg_neg] at hc
  change P.body.m / P.body.M ^ 2 * ‖q‖ ^ 2 ≤ D0 P.body P.electric at hc
  rw [P.material_constants.1, P.material_constants.2] at hc
  have hq : ‖q‖ ^ 2 ≤ P.μ * D0 P.body P.electric := by
    have h := mul_le_mul_of_nonneg_left hc P.μ_pos.le
    convert h using 1; field_simp [P.μ_pos.ne']
  have hq' := mul_le_mul_of_nonneg_left hq (sq_nonneg (1 + P.μ))
  have hfin : P.μ * volume.real P.body.domain ≤ (1 + P.μ) ^ 2 * D0 P.body P.electric := by
    apply (mul_le_mul_iff_right₀ P.μ_pos).mp
    nlinarith only [hNsq, hq']
  exact (div_le_iff₀ (by positivity [P.μ_pos] : 0 < (1 + P.μ) ^ 2)).mpr (by nlinarith only [hfin])

theorem affineCoefficient_lt_two_thousand : affineCoefficient < 2000 := by
  have hs : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  unfold affineCoefficient
  apply (div_lt_iff₀ (by norm_num : 0 < 3 * (4 / 5 : ℝ) ^ 4)).mpr
  have hp := Real.pi_lt_four
  nlinarith only [mul_lt_mul_of_pos_left hs (by positivity : 0 < 256 * Real.pi), hp, Real.pi_pos]

theorem explicit_error_bound : errorCoefficient 1 ≤ 1000000 := by
  have hp := Real.pi_lt_four.le
  have hp2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
  have hc := affineCoefficient_lt_two_thousand.le
  have hc0 := affineCoefficient_pos.le
  unfold errorCoefficient error11 error12 error14 error15
  norm_num only [one_pow, mul_one]
  have h11 : 12 * Real.pi * affineCoefficient ≤ 96000 := by
    calc
      _ ≤ 12 * (4 : ℝ) * 2000 := by gcongr
      _ = _ := by norm_num
  have h12 : 13824 * Real.pi ^ 2 / 5 ≤ (221184 / 5 : ℝ) := by nlinarith only [hp2]
  have h14 : 64 * Real.pi / 9 * affineCoefficient ≤ (512000 / 9 : ℝ) := by
    calc
      _ ≤ 64 * (4 : ℝ) / 9 * 2000 := by gcongr
      _ = _ := by norm_num
  have h15 : 64 * Real.pi / 9 * (576 * Real.pi / 5) ≤ (589824 / 45 : ℝ) := by
    calc
      _ = (36864 / 45) * Real.pi ^ 2 := by ring
      _ ≤ (36864 / 45) * 16 := by gcongr
      _ = _ := by norm_num
  linarith

theorem explicit_leading_lower : 200 ≤ HomogeneousScalars.leading 1 := by
  unfold HomogeneousScalars.leading
  norm_num only [one_pow]
  have hp := Real.pi_gt_three
  nlinarith [Real.pi_pos]

def explicitParameters (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0) : Parameters :=
  ⟨n, e, he, htr, 1, by norm_num, 1 / 100, by norm_num, by norm_num⟩

/-- The original μ=1, a=0.01 finite homogeneous pattern has a strictly
positive actual quartic coefficient, for every real transverse unit pair. -/
theorem explicit_coefficient_pos (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0) :
    0 < FixedPatternContrast.coefficient (explicitParameters n e he htr).body n (complexify e) := by
  let P := explicitParameters n e he htr
  have hsmall : errorCoefficient P.μ * P.a ^ 2 ≤ HomogeneousScalars.leading P.μ / 2 := by
    change errorCoefficient 1 * (1 / 100 : ℝ) ^ 2 ≤ HomogeneousScalars.leading 1 / 2
    nlinarith only [explicit_error_bound, explicit_leading_lower]
  have hI := MomentPerturbation.positive_from_eleventh_order_error P.a_pos
    (HomogeneousScalars.leading_pos P.μ_pos) hsmall P.imaginary_error
  exact P.coefficient_pos hI

end QuarticMaxwell.HomogeneousMoments
