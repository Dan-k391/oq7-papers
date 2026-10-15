import QuarticMaxwell.Schur
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The vector Cauchy--Schwarz integral estimate used by the complete radiation
map. The right-hand measure is the actual finite source measure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set

theorem norm_integral_sq_le_measure_mul_square {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  let q : Lp E 2 μ := hf.toLp f
  let g : Lp ℝ 2 μ := hf.norm.toLp (fun x => ‖f x‖)
  let u : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)
  have hgn : ‖g‖ = ‖q‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable]
  have hu : ‖u‖ ^ 2 = μ.real univ := by
    have h := L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := μ) MeasurableSet.univ MeasurableSet.univ (measure_ne_top μ univ) (measure_ne_top μ univ)
    simpa [u, inner_self_eq_norm_sq_to_K] using h
  have hi : inner ℝ u g = ∫ x, ‖f x‖ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ)
      (hs := MeasurableSet.univ) (hμs := measure_ne_top μ univ) (c := (1 : ℝ)),
      hf.norm.coeFn_toLp] with x hux hgx
    change inner ℝ (u x) (g x) = ‖f x‖
    rw [hux, hgx]
    simp [RCLike.inner_apply]
  have hq : ‖q‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [← lp_integral_norm_sq μ q]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have h := real_inner_le_norm u g
  rw [hi] at h
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg fun x => norm_nonneg _
  have hs : (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ ‖u‖ ^ 2 * ‖g‖ ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg g)]
  have hn := norm_integral_le_integral_norm f (μ := μ)
  have hns : ‖∫ x, f x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := by
    nlinarith [norm_nonneg (∫ x, f x ∂μ)]
  exact hns.trans (by simpa only [hu, hgn, hq] using hs)

end QuarticMaxwell
