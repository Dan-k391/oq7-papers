import QuarticMaxwell.HeterogeneousCertificate
import QuarticMaxwell.HeterogeneousAttainment

/-! Explicit auxiliary continuum enclosures. Decimal endpoints are rounded
outward from the exact rational interval. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.HeterogeneousAuxiliary
open OQ7Prescribed HeterogeneousCertificate FixedPatternWork FixedPatternScattering

def delta (n : UnitSphere) : ℝ := ‖staticResponse (body n) - isolated n‖

theorem delta_nonneg (n : UnitSphere) : 0 ≤ delta n := by unfold delta; positivity

theorem delta_lt (n : UnitSphere) : delta n < 1 / 600 := static_difference n

theorem moment0_error_delta (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖moment0 (body n) e - isolatedMoment0 n e‖ ≤ delta n * volume n := by
  have h := MomentOperator.response_difference_norm_le (body n).domain (body n).finite
    (staticResponse (body n)) (isolated n) (le_refl _) (constantInput (body n) e)
  change ‖moment0 (body n) e - isolatedMoment0 n e‖ ≤
    Real.sqrt (volume n) * delta n * ‖constantInput (body n) e‖ at h
  rw [constant_norm n e he] at h
  apply h.trans
  apply le_of_eq
  calc
    _ = delta n * (Real.sqrt (volume n)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (volume_pos n).le]

theorem moment1_error_delta (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖moment1 (body n) n e - isolatedMoment1 n e‖ ≤ (3 / 5) * delta n * volume n := by
  have h := MomentOperator.response_difference_norm_le (body n).domain (body n).finite
    (staticResponse (body n)) (isolated n) (le_refl _) (linearInput (body n) n e)
  change ‖moment1 (body n) n e - isolatedMoment1 n e‖ ≤
    Real.sqrt (volume n) * delta n * ‖linearInput (body n) n e‖ at h
  apply h.trans
  calc
    _ ≤ Real.sqrt (volume n) * delta n * ((3 / 5) * Real.sqrt (volume n)) :=
      mul_le_mul_of_nonneg_left (linear_norm n e he) (mul_nonneg (Real.sqrt_nonneg _) (delta_nonneg n))
    _ = (3 / 5) * delta n * (Real.sqrt (volume n)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (volume_pos n).le]

theorem imaginary_moment_error_delta (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    |I0 n e + (8 / 195) * volume n ^ 2| ≤
      (3 / 5) * (4 * delta n + delta n ^ 2) * volume n ^ 2 := by
  have h := FixedPatternWork.inner_im_error (moment0 (body n) e) (moment1 (body n) n e)
    (isolatedMoment0 n e) (isolatedMoment1 n e)
  rw [isolated_imaginary_moment n e he] at h
  change |I0 n e - (-(8 / 195) * volume n ^ 2)| ≤ _ at h
  have hn1 : ‖moment1 (body n) n e‖ ≤ (3 / 5) * delta n * volume n + (6 / 5) * volume n := by
    calc
      _ = ‖(moment1 (body n) n e - isolatedMoment1 n e) + isolatedMoment1 n e‖ := by rw [sub_add_cancel]
      _ ≤ ‖moment1 (body n) n e - isolatedMoment1 n e‖ + ‖isolatedMoment1 n e‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (moment1_error_delta n e he) (isolatedMoment1_norm n e he)
  have hδ := delta_nonneg n
  have hV := (volume_pos n).le
  have h' : |I0 n e - (-(8 / 195) * volume n ^ 2)| ≤
      (3 / 5) * (4 * delta n + delta n ^ 2) * volume n ^ 2 := by
    apply h.trans
    calc
      _ ≤ (delta n * volume n) * ((3 / 5) * delta n * volume n + (6 / 5) * volume n) +
          (2 * volume n) * ((3 / 5) * delta n * volume n) := by
        exact add_le_add (mul_le_mul (moment0_error_delta n e he) hn1 (norm_nonneg _) (by positivity))
          (mul_le_mul (isolatedMoment0_norm n e he) (moment1_error_delta n e he) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  simpa only [neg_mul, sub_neg_eq_add] using h'

theorem relative_error_lt_tenth (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    |I0 n e - (inner ℂ (isolatedMoment0 n e) (isolatedMoment1 n e)).im| <
      (1 / 10) * |(inner ℂ (isolatedMoment0 n e) (isolatedMoment1 n e)).im| := by
  rw [isolated_imaginary_moment n e he, neg_mul, abs_neg,
    abs_of_pos (by have hw := volume_pos n; positivity : 0 < (8 / 195 : ℝ) * volume n ^ 2), sub_neg_eq_add]
  have h := imaginary_moment_error n e he
  have hsq := sq_pos_of_pos (volume_pos n)
  nlinarith only [h, hsq]

theorem coefficient_decimal_outward (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    (277109592995 / 10000000000000000 : ℝ) ≤ FixedPatternContrast.coefficient (body n) n e ∧
      FixedPatternContrast.coefficient (body n) n e ≤ 339538921579 / 10000000000000000 := by
  have h := coefficient_interval n e he
  constructor <;> linarith

end QuarticMaxwell.HeterogeneousAuxiliary
