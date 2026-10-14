import PrescribedExtinction.SquareApertureWindow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def squareSmoothWindow (b : ContDiffBump (0 : ℝ)) (z : ℂ) : ℂ :=
  ((b z.re * b z.im : ℝ) : ℂ)

theorem squareSmoothWindow_contDiff (b : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (squareSmoothWindow b) :=
  Complex.ofRealCLM.contDiff.comp
    ((b.contDiff.comp Complex.reCLM.contDiff).mul (b.contDiff.comp Complex.imCLM.contDiff))

theorem squareSmoothWindow_real_bounds (b : ContDiffBump (0 : ℝ)) (z : ℂ) :
    0 ≤ b z.re * b z.im ∧ b z.re * b z.im ≤ 1 := by
  exact ⟨mul_nonneg b.nonneg b.nonneg,
    (mul_le_mul b.le_one b.le_one b.nonneg (by norm_num)).trans_eq (one_mul _)⟩

theorem squareSmoothWindow_support (b : ContDiffBump (0 : ℝ)) (hb : b.rOut < 1 / 2) :
    tsupport (squareSmoothWindow b) ⊆ horizontalSquareAperture 1 := by
  have hs : tsupport (squareSmoothWindow b) ⊆
      {z : ℂ | ‖z.re‖ ≤ b.rOut ∧ ‖z.im‖ ≤ b.rOut} := by
    apply closure_minimal
    · intro z hz
      constructor
      · by_contra hr
        have he : b z.re = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using (lt_of_not_ge hr).le)
        exact hz (by simp [squareSmoothWindow, he])
      · by_contra hi
        have he : b z.im = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using (lt_of_not_ge hi).le)
        exact hz (by simp [squareSmoothWindow, he])
    · exact (isClosed_le Complex.continuous_re.norm continuous_const).inter
        (isClosed_le Complex.continuous_im.norm continuous_const)
  intro z hz
  obtain ⟨hr, hi⟩ := hs hz
  rw [Real.norm_eq_abs] at hr hi
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  change -(1 : ℝ) / 2 < z.re ∧ z.re < 1 / 2 ∧ -(1 : ℝ) / 2 < z.im ∧ z.im < 1 / 2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem squareSmoothWindow_hasCompactSupport (b : ContDiffBump (0 : ℝ)) (hb : b.rOut < 1 / 2) :
    HasCompactSupport (squareSmoothWindow b) :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _) 
    ((squareSmoothWindow_support b hb).trans horizontalSquareAperture_subset_ball)

theorem squareSmoothWindow_one (b : ContDiffBump (0 : ℝ)) (z : ℂ)
    (hz : z ∈ horizontalSquareAperture (2 * b.rIn)) : squareSmoothWindow b z = 1 := by
  change -(2 * b.rIn) / 2 < z.re ∧ z.re < 2 * b.rIn / 2 ∧
    -(2 * b.rIn) / 2 < z.im ∧ z.im < 2 * b.rIn / 2 at hz
  have hr : z.re ∈ Metric.closedBall 0 b.rIn := by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
  have hi : z.im ∈ Metric.closedBall 0 b.rIn := by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  simp [squareSmoothWindow, b.one_of_mem_closedBall hr, b.one_of_mem_closedBall hi]

theorem squareApertureWindow_sub_smooth_norm_le_one (b : ContDiffBump (0 : ℝ))
    (hb : b.rOut < 1 / 2) (z : ℂ) : ‖squareApertureWindow 1 z - squareSmoothWindow b z‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := squareSmoothWindow_real_bounds b z
  by_cases hz : z ∈ horizontalSquareAperture 1
  · change ‖(horizontalSquareAperture 1).indicator (fun _ => (1 : ℂ)) z - ((b z.re * b z.im : ℝ) : ℂ)‖ ≤ 1
    rw [indicator_of_mem hz, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hw : squareSmoothWindow b z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (squareSmoothWindow_support b hb ht))
    simp [squareApertureWindow, indicator_of_notMem hz, hw]

end OQ7Prescribed

