import PrescribedExtinction.BodySeparatedLift
import PrescribedExtinction.ApertureL2Scale

noncomputable section
namespace OQ7Prescribed
open Set

theorem scaledApertureWindow_support_square (w : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    tsupport (scaledApertureWindow w R) ⊆ horizontalSquareAperture R := by
  have hp := tsupport_comp_subset_preimage w (continuous_const_smul R⁻¹ : Continuous (fun z : ℂ => R⁻¹ • z))
  intro z hz
  have hm := hs (hp hz)
  have hcoords : -(1 : ℝ) / 2 < R⁻¹ * z.re ∧ R⁻¹ * z.re < 1 / 2 ∧
      -(1 : ℝ) / 2 < R⁻¹ * z.im ∧ R⁻¹ * z.im < 1 / 2 := by
    simpa [horizontalSquareAperture, Complex.real_smul] using hm
  have hr (t : ℝ) : R * (R⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  change -R / 2 < z.re ∧ z.re < R / 2 ∧ -R / 2 < z.im ∧ z.im < R / 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he := mul_lt_mul_of_pos_left hcoords.1 hR
    rw [hr] at he
    linarith
  · have he := mul_lt_mul_of_pos_left hcoords.2.1 hR
    rw [hr] at he
    linarith
  · have he := mul_lt_mul_of_pos_left hcoords.2.2.1 hR
    rw [hr] at he
    linarith
  · have he := mul_lt_mul_of_pos_left hcoords.2.2.2 hR
    rw [hr] at he
    linarith

theorem horizontalSquareAperture_subset_ball : horizontalSquareAperture 1 ⊆ Metric.closedBall 0 1 := by
  intro z hz
  change -(1 : ℝ) / 2 < z.re ∧ z.re < 1 / 2 ∧ -(1 : ℝ) / 2 < z.im ∧ z.im < 1 / 2 at hz
  have hr : z.re ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hz.1, hz.2.1]
  have hi : z.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hz.2.2.1, hz.2.2.2]
  simp only [Metric.mem_closedBall, dist_zero_right]
  nlinarith [Complex.sq_norm z, Complex.normSq_apply z, norm_nonneg z]

end OQ7Prescribed

