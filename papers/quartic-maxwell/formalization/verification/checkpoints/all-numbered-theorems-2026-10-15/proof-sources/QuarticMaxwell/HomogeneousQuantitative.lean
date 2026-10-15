import QuarticMaxwell.HomogeneousUniform

/-! Literal all-multipole enclosure (62)–(66) for actual homogeneous spheres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed SphereStatic SphereResponse SphereExterior SphereDoubleMean
  BlockSourceMoments BlockInteractionMoments TwoSupportStatic TwoSupportBounds TwoSphereGeometry
  SourceTaylor FixedPatternWork FixedPatternScattering MeasureTheory Set

theorem Parameters.p1c_beta_norm (P : Parameters) :
    ‖P.p1c‖ ≤ affineCoefficient * ‖beta (HomogeneousScalars.contrast P.μ)‖ * P.μ * P.a ^ 8 := by
  have h := first_affine_moment (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) (gap P.a) (gap_pos P.a_small) P.center_separation
    (sphere_separation P.n P.a) P.material P.n P.electric (3 / 5) (domain_subset P.n P.a_small)
  change P.p1c = _ at h
  rw [P.center_projection_left, P.center_projection_right] at h
  norm_num only [neg_div, neg_add_cancel, zero_mul, Complex.ofReal_zero, mul_zero, zero_smul, zero_add] at h
  dsimp only [Parameters.material, homogeneousPair] at h
  have hL := first_odd_cross_norm (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) (gap P.a) (gap_pos P.a_small) P.center_separation
    (sphere_separation P.n P.a) P.μ P.μ_pos (P.n : OQ7Prescribed.Position) (by simp)
    P.electric P.electric_norm
  have hR := first_odd_cross_norm (rightCenter P.n) (leftCenter P.n) (2 * P.a) P.a
    (by linarith [P.a_pos]) P.a_pos (gap P.a) (gap_pos P.a_small)
    (by rw [norm_sub_rev]; linarith [P.center_separation]) P.reverse_separation
    P.μ P.μ_pos (P.n : OQ7Prescribed.Position) (by simp) P.electric P.electric_norm
  rw [ball_inverse_moment _ _ P.a_pos] at hL
  rw [ball_inverse_moment _ _ (by linarith [P.a_pos] : 0 < 2 * P.a)] at hR
  have hsum := (norm_add_le _ _).trans (add_le_add hL hR)
  change ‖_ + _‖ ≤ _ at hsum
  rw [← h] at hsum
  rw [ball_volume_real (leftCenter P.n) P.a_pos.le,
    ball_volume_real (rightCenter P.n) (by linarith [P.a_pos] : 0 ≤ 2 * P.a)] at hsum
  have hgap : (4 / 5 : ℝ) ≤ gap P.a := by unfold gap; linarith [P.a_small]
  have hfactor : 6 * Real.sqrt 3 / (5 * Real.pi * (gap P.a) ^ 4) ≤
      6 * Real.sqrt 3 / (5 * Real.pi * (4 / 5 : ℝ) ^ 4) := by gcongr
  apply hsum.trans
  calc
    _ ≤ (6 * Real.sqrt 3 / (5 * Real.pi * (4 / 5 : ℝ) ^ 4)) * ‖beta (HomogeneousScalars.contrast P.μ)‖ * P.μ * (2 * P.a) ^ 2 *
          (4 * Real.pi * P.a ^ 3 / 3) * (4 * Real.pi * (2 * P.a) ^ 3 / 3) +
        (6 * Real.sqrt 3 / (5 * Real.pi * (4 / 5 : ℝ) ^ 4)) * ‖beta (HomogeneousScalars.contrast P.μ)‖ * P.μ * P.a ^ 2 *
          (4 * Real.pi * (2 * P.a) ^ 3 / 3) * (4 * Real.pi * P.a ^ 3 / 3) := by
      gcongr <;> first | exact hfactor | exact le_rfl | positivity [P.μ_pos, P.a_pos]
    _ = _ := by unfold affineCoefficient; field_simp [Real.pi_ne_zero]; ring

theorem Parameters.p0b_beta_norm (P : Parameters) :
    ‖P.p0b‖ = ‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3) := by
  rw [P.p0b_formula, norm_smul, P.electric_norm, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity [P.a_pos] : 0 ≤ 12 * Real.pi * P.a ^ 3)]

theorem Parameters.p0c_beta_norm (P : Parameters) :
    ‖P.p0c‖ = (64 * Real.pi / 9) * ‖beta (HomogeneousScalars.contrast P.μ)‖ ^ 2 * P.a ^ 6 := by
  rw [P.p0c_formula, norm_smul, P.electric_norm, mul_one]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 64 * Real.pi / 9),
    abs_of_nonneg (by positivity [P.a_pos] : 0 ≤ P.a)]

theorem Parameters.approx0_beta_norm (P : Parameters) :
    ‖P.p0b + P.p0c‖ ≤ 2 * ‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3) := by
  have hfactor : (16 / 27 : ℝ) * ‖beta (HomogeneousScalars.contrast P.μ)‖ * P.a ^ 3 ≤ 1 := by
    calc
      _ ≤ (16 / 27 : ℝ) * 3 * (1 / 20 : ℝ) ^ 3 := by
        gcongr <;> first | exact HomogeneousScalars.beta_norm_le_three P.μ | exact P.a_small | positivity [P.a_pos]
      _ ≤ _ := by norm_num
  have hc : ‖P.p0c‖ ≤ ‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3) := by
    calc
      _ = (‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3)) *
          ((16 / 27 : ℝ) * ‖beta (HomogeneousScalars.contrast P.μ)‖ * P.a ^ 3) := by rw [P.p0c_beta_norm]; ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor (by positivity [P.a_pos])
  calc
    _ ≤ ‖P.p0b‖ + ‖P.p0c‖ := norm_add_le _ _
    _ ≤ ‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3) +
        ‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3) := by rw [P.p0b_beta_norm]; exact add_le_add le_rfl hc
    _ = _ := by ring

def Parameters.approx1 (P : Parameters) : Vector := P.p1b + P.p1c

theorem Parameters.first_interaction_error (P : Parameters) :
    |(inner ℂ (P.p0b + P.p0c) P.approx1).im - HomogeneousScalars.leading P.μ * P.a ^ 9| ≤
      (HomogeneousScalars.leading P.μ * P.a ^ 9) * (30 * (9 + P.μ ^ 2) * P.a ^ 2) := by
  have h := inner_im_error (P.p0b + P.p0c) P.approx1 (P.p0b + P.p0c) P.p1b
  simp only [sub_self, norm_zero, zero_mul, zero_add, Parameters.approx1, add_sub_cancel_left,
    P.leading_moment] at h
  apply h.trans
  calc
    _ ≤ (2 * ‖beta (HomogeneousScalars.contrast P.μ)‖ * (12 * Real.pi * P.a ^ 3)) *
        (affineCoefficient * ‖beta (HomogeneousScalars.contrast P.μ)‖ * P.μ * P.a ^ 8) := by
      exact mul_le_mul P.approx0_beta_norm P.p1c_beta_norm (norm_nonneg _) (by positivity [P.a_pos])
    _ = (HomogeneousScalars.leading P.μ * P.a ^ 9) *
        ((48 * Real.sqrt 3 / (7 * (4 / 5 : ℝ) ^ 4)) * (9 + P.μ ^ 2) * P.a ^ 2) := by
      have hβ := HomogeneousScalars.beta_norm_sq P.μ
      unfold affineCoefficient HomogeneousScalars.leading
      calc
        _ = (24 * Real.pi * affineCoefficient * P.μ * P.a ^ 11) *
            ‖beta (HomogeneousScalars.contrast P.μ)‖ ^ 2 := by unfold affineCoefficient; ring
        _ = _ := by rw [hβ]; unfold affineCoefficient; field_simp; ring
    _ ≤ _ := by
      have hL := HomogeneousScalars.leading_pos P.μ_pos
      gcongr <;> first | exact OQ7Quartic.first_interaction_error.le | positivity [P.a_pos]


theorem Parameters.approx0_mu_norm (P : Parameters) :
    ‖P.p0b + P.p0c‖ ≤ 24 * Real.pi * P.μ * P.a ^ 3 := by
  apply P.approx0_beta_norm.trans
  calc
    _ ≤ 2 * P.μ * (12 * Real.pi * P.a ^ 3) := by
      gcongr <;> first | exact HomogeneousScalars.beta_norm_le_mu P.μ_pos.le | positivity [P.a_pos]
    _ = _ := by ring

theorem Parameters.remaining_interaction_error (P : Parameters) :
    |(inner ℂ P.p0 P.p1).im - (inner ℂ (P.p0b + P.p0c) P.approx1).im| ≤
      (HomogeneousScalars.leading P.μ * P.a ^ 9) * ((54 / 35 : ℝ) * P.μ * (9 + P.μ ^ 2) ^ 2 * P.a ^ 3) := by
  have h0 : ‖P.p0 - (P.p0b + P.p0c)‖ ≤ 192 * Real.pi * P.μ ^ 3 * P.a ^ 9 := by
    simpa only [sub_add_eq_sub_sub] using P.p0_error
  have h1 : ‖P.p1 - P.approx1‖ ≤ (576 * Real.pi / 5) * P.μ ^ 3 * P.a ^ 9 := by
    simpa only [Parameters.approx1, sub_add_eq_sub_sub] using P.p1_error
  have h := MomentPerturbation.imaginary_error P.p0 P.p1 (P.p0b + P.p0c) P.approx1
    (inner ℂ (P.p0b + P.p0c) P.approx1).im
    (192 * Real.pi * P.μ ^ 3 * P.a ^ 9) ((576 * Real.pi / 5) * P.μ ^ 3 * P.a ^ 9)
    (24 * Real.pi * P.μ * P.a ^ 3) ((36 * Real.pi / 5) * P.μ * P.a ^ 3)
    rfl h0 h1 P.approx0_mu_norm P.p1_norm
  apply h.trans_eq
  unfold HomogeneousScalars.leading
  field_simp
  ring

/-- Literal original Eq. (64), for the exact continuum two-sphere inverse. -/
theorem Parameters.quantitative_relative_error (P : Parameters) :
    |(inner ℂ P.p0 P.p1).im - HomogeneousScalars.leading P.μ * P.a ^ 9| /
      (HomogeneousScalars.leading P.μ * P.a ^ 9) ≤
        30 * (9 + P.μ ^ 2) * P.a ^ 2 + (54 / 35 : ℝ) * P.μ * (9 + P.μ ^ 2) ^ 2 * P.a ^ 3 := by
  have hL := HomogeneousScalars.leading_pos P.μ_pos
  apply (div_le_iff₀ (by positivity [P.a_pos] : 0 < HomogeneousScalars.leading P.μ * P.a ^ 9)).mpr
  calc
    _ ≤ |(inner ℂ P.p0 P.p1).im - (inner ℂ (P.p0b + P.p0c) P.approx1).im| +
        |(inner ℂ (P.p0b + P.p0c) P.approx1).im - HomogeneousScalars.leading P.μ * P.a ^ 9| := abs_sub_le _ _ _
    _ ≤ (HomogeneousScalars.leading P.μ * P.a ^ 9) *
          ((54 / 35 : ℝ) * P.μ * (9 + P.μ ^ 2) ^ 2 * P.a ^ 3) +
        (HomogeneousScalars.leading P.μ * P.a ^ 9) * (30 * (9 + P.μ ^ 2) * P.a ^ 2) :=
      add_le_add P.remaining_interaction_error P.first_interaction_error
    _ = _ := by ring

theorem explicit_relative_error (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0) :
    let P := explicitParameters n e he htr
    |(inner ℂ P.p0 P.p1).im - HomogeneousScalars.leading P.μ * P.a ^ 9| /
      (HomogeneousScalars.leading P.μ * P.a ^ 9) ≤ 5277 / 175000 := by
  apply (explicitParameters n e he htr).quantitative_relative_error.trans_eq
  change (30 : ℝ) * (9 + 1 ^ 2) * (1 / 100) ^ 2 + (54 / 35) * 1 * (9 + 1 ^ 2) ^ 2 * (1 / 100) ^ 3 = _
  norm_num

theorem Parameters.quantitative_enclosure (P : Parameters)
    (hsize2 : P.a ^ 2 ≤ 1 / (120 * (9 + P.μ ^ 2)))
    (hsize3 : P.a ^ 3 ≤ 35 / (216 * P.μ * (9 + P.μ ^ 2) ^ 2)) :
    (HomogeneousScalars.leading P.μ / 2) * P.a ^ 9 ≤ (inner ℂ P.p0 P.p1).im ∧
      (inner ℂ P.p0 P.p1).im ≤ (3 * HomogeneousScalars.leading P.μ / 2) * P.a ^ 9 := by
  have hA : 30 * (9 + P.μ ^ 2) * P.a ^ 2 ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left hsize2 (by positivity)).trans_eq
    field_simp
    norm_num
  have hB : (54 / 35 : ℝ) * P.μ * (9 + P.μ ^ 2) ^ 2 * P.a ^ 3 ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left hsize3 (by positivity [P.μ_pos])).trans_eq
    field_simp [P.μ_pos.ne']
    ring
  have hL := HomogeneousScalars.leading_pos P.μ_pos
  have hErr := P.quantitative_relative_error.trans (show _ ≤ (1 / 2 : ℝ) by linarith)
  have hAbs := (div_le_iff₀ (by positivity [P.a_pos] : 0 < HomogeneousScalars.leading P.μ * P.a ^ 9)).mp hErr
  have h := abs_le.mp hAbs
  constructor <;> linarith


/-- Literal original Eq. (66), including both constants, for the actual
continuum quartic coefficient under the stated fixed-radius restrictions. -/
theorem Parameters.quantitative_coefficient_interval (P : Parameters)
    (hsize2 : P.a ^ 2 ≤ 1 / (120 * (9 + P.μ ^ 2)))
    (hsize3 : P.a ^ 3 ≤ 35 / (216 * P.μ * (9 + P.μ ^ 2) ^ 2)) :
    (224 * P.μ ^ 2 / (3 * (9 + P.μ ^ 2) ^ 2)) * P.a ^ 6 ≤
        FixedPatternContrast.coefficient P.body P.n P.electric ∧
    FixedPatternContrast.coefficient P.body P.n P.electric ≤
        (224 * P.μ ^ 2 * (1 + P.μ) ^ 2 / (9 + P.μ ^ 2) ^ 2) * P.a ^ 6 := by
  have hI := P.quantitative_enclosure hsize2 hsize3
  have hL := HomogeneousScalars.leading_pos P.μ_pos
  have hIpos : 0 < (inner ℂ P.p0 P.p1).im := lt_of_lt_of_le (by positivity [P.a_pos]) hI.1
  have hV : 0 < volume.real P.body.domain := by rw [P.body_volume]; positivity [P.a_pos]
  have hD := D0_pos P.body hV P.n P.electric P.electric_norm
  constructor
  · convert P.coefficient_lower hI.1 using 1
    unfold coefficientFloor HomogeneousScalars.leading
    field_simp [P.μ_pos.ne', Real.pi_ne_zero]
    ring
  · unfold FixedPatternContrast.coefficient FixedPatternScattering.leading
    change |(2 / (3 * Real.pi)) * (inner ℂ P.p0 P.p1).im| / D0 P.body P.electric ≤ _
    rw [abs_of_nonneg (mul_nonneg (by positivity) hIpos.le)]
    apply (div_le_iff₀ hD).mpr
    calc
      _ ≤ (2 / (3 * Real.pi)) * ((3 * HomogeneousScalars.leading P.μ / 2) * P.a ^ 9) :=
        mul_le_mul_of_nonneg_left hI.2 (by positivity)
      _ = ((224 * P.μ ^ 2 * (1 + P.μ) ^ 2 / (9 + P.μ ^ 2) ^ 2) * P.a ^ 6) *
          (P.μ * volume.real P.body.domain / (1 + P.μ) ^ 2) := by
        rw [P.body_volume]
        unfold HomogeneousScalars.leading
        field_simp [Real.pi_ne_zero, P.μ_pos.ne', (by positivity [P.μ_pos] : (1 + P.μ : ℝ) ≠ 0)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left P.denominator_lower (by positivity [P.a_pos])


/-- Positive radii satisfying all the original fixed-radius restrictions
exist for every fixed μ>0. The choice depends only on μ. -/
theorem exists_quantitative_radius (μ : ℝ) (hμ : 0 < μ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 20 ∧ a ^ 2 ≤ 1 / (120 * (9 + μ ^ 2)) ∧
      a ^ 3 ≤ 35 / (216 * μ * (9 + μ ^ 2) ^ 2) := by
  let A : ℝ := 1 / (120 * (9 + μ ^ 2))
  let B : ℝ := 35 / (216 * μ * (9 + μ ^ 2) ^ 2)
  have hA : 0 < A := by unfold A; positivity
  have hB : 0 < B := by unfold B; positivity
  let a := min (1 / 20 : ℝ) (min A B)
  have ha : 0 < a := lt_min (by norm_num) (lt_min hA hB)
  have ha20 : a ≤ (1 / 20 : ℝ) := min_le_left _ _
  have ha1 : a ≤ 1 := by linarith
  have h2 : a ^ 2 ≤ a := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  have h3 : a ^ 3 ≤ a := by
    apply le_trans _ h2
    calc
      _ = a ^ 2 * a := by ring
      _ ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
      _ = _ := mul_one _
  refine ⟨a, ha, ha20, h2.trans ?_, h3.trans ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem exists_quantitative_parameters (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0)
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ P : Parameters, P.n = n ∧ P.e = e ∧ P.μ = μ ∧
      (224 * μ ^ 2 / (3 * (9 + μ ^ 2) ^ 2)) * P.a ^ 6 ≤
        FixedPatternContrast.coefficient P.body n (complexify e) ∧
      FixedPatternContrast.coefficient P.body n (complexify e) ≤
        (224 * μ ^ 2 * (1 + μ) ^ 2 / (9 + μ ^ 2) ^ 2) * P.a ^ 6 := by
  obtain ⟨a, ha, ha20, h2, h3⟩ := exists_quantitative_radius μ hμ
  let P : Parameters := ⟨n, e, he, htr, μ, hμ, a, ha, ha20⟩
  exact ⟨P, rfl, rfl, rfl, P.quantitative_coefficient_interval h2 h3⟩

end QuarticMaxwell.HomogeneousMoments
