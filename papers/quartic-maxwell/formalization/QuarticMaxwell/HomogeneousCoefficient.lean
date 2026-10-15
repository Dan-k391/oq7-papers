import QuarticMaxwell.HomogeneousErrors
import QuarticMaxwell.MomentPerturbation
import QuarticMaxwell.FixedPatternContrast

/-! Actual homogeneous finite-sphere positive quartic coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed SphereStatic SphereResponse SphereExterior SphereDoubleMean
  BlockSourceMoments BlockInteractionMoments TwoSupportStatic TwoSupportBounds TwoSphereGeometry
  SourceTaylor FixedPatternWork FixedPatternScattering MeasureTheory Set

def error11 (μ : ℝ) : ℝ := 12 * Real.pi * affineCoefficient * μ ^ 3

def error12 (μ : ℝ) : ℝ := (13824 * Real.pi ^ 2 / 5) * μ ^ 4

def error14 (μ : ℝ) : ℝ := (64 * Real.pi / 9) * affineCoefficient * μ ^ 4

def error15 (μ : ℝ) : ℝ := (64 * Real.pi / 9) * (576 * Real.pi / 5) * μ ^ 5

def errorCoefficient (μ : ℝ) : ℝ := error11 μ + error12 μ + error14 μ + error15 μ

theorem errorCoefficient_nonneg {μ : ℝ} (hμ : 0 < μ) : 0 ≤ errorCoefficient μ := by
  have hc := affineCoefficient_pos
  unfold errorCoefficient error11 error12 error14 error15
  positivity

theorem Parameters.imaginary_error (P : Parameters) :
    |(inner ℂ P.p0 P.p1).im - HomogeneousScalars.leading P.μ * P.a ^ 9| ≤
      errorCoefficient P.μ * P.a ^ 11 := by
  have h0 : ‖P.p0 - (P.p0b + P.p0c)‖ ≤ 192 * Real.pi * P.μ ^ 3 * P.a ^ 9 := by
    simpa only [sub_add_eq_sub_sub] using P.p0_error
  have h := MomentPerturbation.imaginary_error_split P.p0 P.p1 (P.p0b + P.p0c) P.p1b
    (HomogeneousScalars.leading P.μ * P.a ^ 9)
    (192 * Real.pi * P.μ ^ 3 * P.a ^ 9) (affineCoefficient * P.μ ^ 2 * P.a ^ 8)
    ((576 * Real.pi / 5) * P.μ ^ 3 * P.a ^ 9)
    (12 * Real.pi * P.μ * P.a ^ 3 + (64 * Real.pi / 9) * P.μ ^ 2 * P.a ^ 6)
    ((36 * Real.pi / 5) * P.μ * P.a ^ 3)
    P.leading_moment h0 P.p1_difference P.approx0_norm P.p1_norm
  have hpoly : |(inner ℂ P.p0 P.p1).im - HomogeneousScalars.leading P.μ * P.a ^ 9| ≤
      error11 P.μ * P.a ^ 11 + error12 P.μ * P.a ^ 12 +
        error14 P.μ * P.a ^ 14 + error15 P.μ * P.a ^ 15 := by
    convert h using 1
    unfold error11 error12 error14 error15
    ring
  apply MomentPerturbation.higher_power_collapse P.a_pos.le (by linarith [P.a_small]) _ _ _ hpoly
  · unfold error12; positivity [P.μ_pos]
  · have hc := affineCoefficient_pos; unfold error14; positivity [P.μ_pos]
  · unfold error15; positivity [P.μ_pos]

theorem Parameters.coefficient_pos (P : Parameters)
    (hI : 0 < (inner ℂ P.p0 P.p1).im) :
    0 < FixedPatternContrast.coefficient P.body P.n P.electric := by
  have hV : 0 < volume.real P.body.domain := by rw [P.body_volume]; positivity [P.a_pos]
  have hD := D0_pos P.body hV P.n P.electric P.electric_norm
  unfold FixedPatternContrast.coefficient FixedPatternScattering.leading
  change 0 < |(2 / (3 * Real.pi)) * (inner ℂ P.p0 P.p1).im| / D0 P.body P.electric
  exact div_pos (abs_pos.mpr (ne_of_gt (mul_pos (by positivity) hI))) hD

/-- The radius is chosen from proved continuum errors, before taking the
physical shrinking-body limit. No target coefficient is a parameter field. -/
theorem exists_positive_coefficient (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0)
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ P : Parameters, P.n = n ∧ P.e = e ∧ P.μ = μ ∧
      0 < FixedPatternContrast.coefficient P.body P.n P.electric := by
  obtain ⟨a, ha, hsmall, hKa⟩ := MomentPerturbation.exists_small_square
    (A := (1 / 20 : ℝ)) (L := HomogeneousScalars.leading μ) (K := errorCoefficient μ)
    (by norm_num) (HomogeneousScalars.leading_pos hμ) (errorCoefficient_nonneg hμ)
  let P : Parameters := ⟨n, e, he, htr, μ, hμ, a, ha, hsmall⟩
  have hI := MomentPerturbation.positive_from_eleventh_order_error ha
    (HomogeneousScalars.leading_pos hμ) hKa P.imaginary_error
  exact ⟨P, rfl, rfl, rfl, P.coefficient_pos hI⟩


def chosenRadius (μ : ℝ) (hμ : 0 < μ) : ℝ :=
  Classical.choose (MomentPerturbation.exists_small_square
    (A := (1 / 20 : ℝ)) (L := HomogeneousScalars.leading μ) (K := errorCoefficient μ)
    (by norm_num) (HomogeneousScalars.leading_pos hμ) (errorCoefficient_nonneg hμ))

theorem chosenRadius_spec (μ : ℝ) (hμ : 0 < μ) :
    0 < chosenRadius μ hμ ∧ chosenRadius μ hμ ≤ 1 / 20 ∧
      errorCoefficient μ * (chosenRadius μ hμ) ^ 2 ≤ HomogeneousScalars.leading μ / 2 :=
  Classical.choose_spec (MomentPerturbation.exists_small_square
    (A := (1 / 20 : ℝ)) (L := HomogeneousScalars.leading μ) (K := errorCoefficient μ)
    (by norm_num) (HomogeneousScalars.leading_pos hμ) (errorCoefficient_nonneg hμ))

def chosenParameters (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0)
    (μ : ℝ) (hμ : 0 < μ) : Parameters :=
  ⟨n, e, he, htr, μ, hμ, chosenRadius μ hμ, (chosenRadius_spec μ hμ).1,
    (chosenRadius_spec μ hμ).2.1⟩

def coefficientFloor (μ a : ℝ) : ℝ := HomogeneousScalars.leading μ * a ^ 6 / (36 * Real.pi ^ 2 * μ)

theorem coefficientFloor_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) : 0 < coefficientFloor μ a := by
  have hL := HomogeneousScalars.leading_pos hμ
  unfold coefficientFloor
  positivity

theorem Parameters.denominator_upper (P : Parameters) :
    D0 P.body P.electric ≤ 12 * Real.pi * P.μ * P.a ^ 3 := by
  change (inner ℂ P.f0 (staticResponse P.body P.f0)).im ≤ _
  calc
    _ ≤ ‖inner ℂ P.f0 (staticResponse P.body P.f0)‖ := Complex.im_le_norm _
    _ ≤ ‖P.f0‖ * ‖staticResponse P.body P.f0‖ := norm_inner_le_norm _ _
    _ ≤ ‖P.f0‖ * (P.μ * ‖P.f0‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((staticResponse P.body).le_opNorm P.f0).trans
        (mul_le_mul_of_nonneg_right P.static_norm (norm_nonneg _))
    _ = P.μ * (Real.sqrt (volume.real P.body.domain)) ^ 2 := by rw [P.f0_norm]; ring
    _ = _ := by rw [Real.sq_sqrt measureReal_nonneg, P.body_volume]; ring

theorem Parameters.coefficient_lower (P : Parameters)
    (hI : (HomogeneousScalars.leading P.μ / 2) * P.a ^ 9 ≤ (inner ℂ P.p0 P.p1).im) :
    coefficientFloor P.μ P.a ≤ FixedPatternContrast.coefficient P.body P.n P.electric := by
  have hV : 0 < volume.real P.body.domain := by rw [P.body_volume]; positivity [P.a_pos]
  have hD := D0_pos P.body hV P.n P.electric P.electric_norm
  have hL := HomogeneousScalars.leading_pos P.μ_pos
  have hIpos : 0 < (inner ℂ P.p0 P.p1).im := lt_of_lt_of_le (by positivity [P.a_pos]) hI
  unfold FixedPatternContrast.coefficient FixedPatternScattering.leading
  change coefficientFloor P.μ P.a ≤ |(2 / (3 * Real.pi)) * (inner ℂ P.p0 P.p1).im| / D0 P.body P.electric
  rw [abs_of_nonneg (mul_nonneg (by positivity) hIpos.le)]
  apply (le_div_iff₀ hD).mpr
  calc
    _ ≤ coefficientFloor P.μ P.a * (12 * Real.pi * P.μ * P.a ^ 3) :=
      mul_le_mul_of_nonneg_left P.denominator_upper (coefficientFloor_pos P.μ_pos P.a_pos).le
    _ = (2 / (3 * Real.pi)) * ((HomogeneousScalars.leading P.μ / 2) * P.a ^ 9) := by
      unfold coefficientFloor
      field_simp [Real.pi_ne_zero, P.μ_pos.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (by positivity)

/-- One actual sphere radius, depending only on μ, works simultaneously for
all real unit incident directions and real unit transverse polarizations. -/
theorem chosen_coefficient_lower (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0)
    (μ : ℝ) (hμ : 0 < μ) :
    coefficientFloor μ (chosenRadius μ hμ) ≤
      FixedPatternContrast.coefficient (chosenParameters n e he htr μ hμ).body n (complexify e) := by
  let P := chosenParameters n e he htr μ hμ
  have hI := (MomentPerturbation.eleventh_order_enclosure P.a_pos (chosenRadius_spec μ hμ).2.2 P.imaginary_error).1
  exact P.coefficient_lower hI

theorem chosen_coefficient_pos (n : UnitSphere) (e : OQ7Prescribed.Position)
    (he : ‖e‖ = 1) (htr : inner ℝ (n : OQ7Prescribed.Position) e = 0)
    (μ : ℝ) (hμ : 0 < μ) :
    0 < FixedPatternContrast.coefficient (chosenParameters n e he htr μ hμ).body n (complexify e) :=
  lt_of_lt_of_le (coefficientFloor_pos hμ (chosenRadius_spec μ hμ).1)
    (chosen_coefficient_lower n e he htr μ hμ)

end QuarticMaxwell.HomogeneousMoments
