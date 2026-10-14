import PrescribedExtinction.SquareSmoothWindow

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

theorem horizontalSquareAperture_mono {R S : ℝ} (h : R ≤ S) :
    horizontalSquareAperture R ⊆ horizontalSquareAperture S := by
  intro z hz
  change -R / 2 < z.re ∧ z.re < R / 2 ∧ -R / 2 < z.im ∧ z.im < R / 2 at hz
  change -S / 2 < z.re ∧ z.re < S / 2 ∧ -S / 2 < z.im ∧ z.im < S / 2
  exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩

theorem squareApertureWindow_integral_norm_sq (R : ℝ) (hR : 0 ≤ R) :
    (∫ z : ℂ, ‖squareApertureWindow R z‖ ^ 2) = R ^ 2 := by
  have he : (fun z : ℂ => ‖squareApertureWindow R z‖ ^ 2) =
      (horizontalSquareAperture R).indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hz : z ∈ horizontalSquareAperture R <;> simp [squareApertureWindow, hz]
  rw [he, integral_indicator (horizontalSquareAperture_isOpen R).measurableSet, integral_const]
  change ((volume.restrict (horizontalSquareAperture R)) univ).toReal • (1 : ℝ) = _
  rw [Measure.restrict_apply_univ, horizontalSquareAperture_volume R hR,
    ENNReal.toReal_ofReal (sq_nonneg R), smul_eq_mul, mul_one]

theorem squareSmoothWindow_L2_error_sq (b : ContDiffBump (0 : ℝ)) (hb : b.rOut < 1 / 2) :
    ‖((squareApertureWindow_memLp 1).sub ((squareSmoothWindow_contDiff b).continuous.memLp_of_hasCompactSupport
      (p := 2) (μ := volume) (squareSmoothWindow_hasCompactSupport b hb))).toLp
        (squareApertureWindow 1 - squareSmoothWindow b)‖ ^ 2 ≤ 1 - (2 * b.rIn) ^ 2 := by
  have hsub : horizontalSquareAperture (2 * b.rIn) ⊆ horizontalSquareAperture 1 :=
    horizontalSquareAperture_mono (by linarith [b.rIn_lt_rOut])
  let m := (squareApertureWindow_memLp 1).sub ((squareSmoothWindow_contDiff b).continuous.memLp_of_hasCompactSupport
    (p := 2) (μ := volume) (squareSmoothWindow_hasCompactSupport b hb))
  have hg := (memLp_two_iff_integrable_sq_norm m.aestronglyMeasurable).mp m
  have hi := (memLp_two_iff_integrable_sq_norm (squareApertureWindow_memLp 1).aestronglyMeasurable).mp (squareApertureWindow_memLp 1)
  have hj := (memLp_two_iff_integrable_sq_norm (squareApertureWindow_memLp (2 * b.rIn)).aestronglyMeasurable).mp (squareApertureWindow_memLp (2 * b.rIn))
  have hpoint (z : ℂ) : ‖(squareApertureWindow 1 - squareSmoothWindow b) z‖ ^ 2 ≤
      ‖squareApertureWindow 1 z‖ ^ 2 - ‖squareApertureWindow (2 * b.rIn) z‖ ^ 2 := by
    by_cases hin : z ∈ horizontalSquareAperture (2 * b.rIn)
    · simp [Pi.sub_apply, squareSmoothWindow_one b z hin, squareApertureWindow, hin, hsub hin]
    · by_cases hout : z ∈ horizontalSquareAperture 1
      · have hn := squareApertureWindow_sub_smooth_norm_le_one b hb z
        simp only [squareApertureWindow, indicator_of_mem hout, indicator_of_notMem hin, norm_one,
          one_pow, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
        change ‖squareApertureWindow 1 z - squareSmoothWindow b z‖ ^ 2 ≤ 1
        nlinarith [norm_nonneg (squareApertureWindow 1 z - squareSmoothWindow b z)]
      · have hw : squareSmoothWindow b z = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hout (squareSmoothWindow_support b hb ht))
        simp [Pi.sub_apply, squareApertureWindow, hin, hout, hw]
  have he := integral_mono_ae hg (hi.sub hj) (ae_of_all _ hpoint)
  simp only [Pi.sub_apply] at he
  rw [integral_sub hi hj, squareApertureWindow_integral_norm_sq 1 (by norm_num),
    squareApertureWindow_integral_norm_sq (2 * b.rIn) (mul_nonneg (by norm_num) b.rIn_pos.le), one_pow] at he
  change (∫ z : ℂ, ‖(squareApertureWindow 1 - squareSmoothWindow b) z‖ ^ 2) ≤ 1 - (2 * b.rIn) ^ 2 at he
  rw [memLp_two_integral_norm_sq _ m] at he
  exact he

theorem squareApertureWindow_smooth_L2_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w),
      tsupport w ⊆ horizontalSquareAperture 1 ∧
        ‖((squareApertureWindow_memLp 1).sub
          (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp
            (squareApertureWindow 1 - w)‖ < ε := by
  let τ : ℝ := min (ε ^ 2 / 8) (1 / 8)
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτsmall : τ ≤ 1 / 8 := min_le_right _ _
  have hτε : τ ≤ ε ^ 2 / 8 := min_le_left _ _
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2 - τ, 1 / 2 - τ / 2, by linarith, by linarith⟩
  have hb : b.rOut < 1 / 2 := by change 1 / 2 - τ / 2 < 1 / 2; linarith
  let hw := squareSmoothWindow_contDiff b
  let hwc := squareSmoothWindow_hasCompactSupport b hb
  refine ⟨squareSmoothWindow b, hw, hwc, squareSmoothWindow_support b hb, ?_⟩
  have he := squareSmoothWindow_L2_error_sq b hb
  change ‖_‖ ^ 2 ≤ 1 - (2 * (1 / 2 - τ)) ^ 2 at he
  have hn := norm_nonneg (((squareApertureWindow_memLp 1).sub
    (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp
      (squareApertureWindow 1 - squareSmoothWindow b))
  nlinarith [sq_pos_of_pos hε]

end OQ7Prescribed

