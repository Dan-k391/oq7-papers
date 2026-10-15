import QuarticMaxwell.SourceTaylor
import QuarticMaxwell.SharpVolume
import QuarticMaxwell.RadiationMoment
import PrescribedExtinction.NewtonPV
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact actual-volume moments of centered affine sources on open balls. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QuarticMaxwell.BallAffineMoments
open MeasureTheory Set OQ7Prescribed

theorem ball_measure_ne_top (c : Position) (a : ℝ) : volume (Metric.ball c a) ≠ ⊤ :=
  ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall c a).measure_lt_top).ne

theorem sphere_real_inner_square (n : Position) :
    (∫ u : UnitSphere, (inner ℝ n (u : Position)) ^ 2 ∂sphereArea) = 4 * Real.pi / 3 * ‖n‖ ^ 2 := by
  have h := sphere_inner_norm_sq (complexify n)
  rw [complexify_norm] at h
  apply Eq.trans _ h
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    have he : inner ℂ (complexify u) (complexify n) = ((inner ℝ (u : Position) n : ℝ) : ℂ) := by
      simp [PiLp.inner_apply, RCLike.inner_apply, complexify]
    change (inner ℝ n (u : Position)) ^ 2 = ‖inner ℂ (complexify u) (complexify n)‖ ^ 2
    rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs, real_inner_comm n (u : Position)]

theorem radial_second_moment (a : ℝ) (ha : 0 < a) :
    (∫ r : Ioi (0 : ℝ), (Iio a).indicator (fun t : ℝ => t ^ 2) r.1 ∂Measure.volumeIoiPow 2) = a ^ 5 / 5 := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ 2)))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun r : Ioi (0 : ℝ) => (ENNReal.ofReal (r.1 ^ 2)).toReal •
      (Iio a).indicator (fun t : ℝ => t ^ 2) r.1) =
      (fun r : Ioi (0 : ℝ) => (Iio a).indicator (fun t : ℝ => t ^ 4) r.1) := by
    funext r
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    by_cases hr : r.1 < a
    · simp [indicator, hr, smul_eq_mul, pow_succ]
      ring
    · simp [indicator, hr]
  rw [he, integral_subtype_comap measurableSet_Ioi,
    setIntegral_indicator measurableSet_Iio]
  have hset : Ioi (0 : ℝ) ∩ Iio a = Ioo (0 : ℝ) a := by ext r; simp
  rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le, integral_pow]
  norm_num

theorem ball_zero_inner_square (a : ℝ) (ha : 0 < a) (n : Position) :
    (∫ x in Metric.ball (0 : Position) a, (inner ℝ n x) ^ 2) =
      volume.real (Metric.ball (0 : Position) a) * a ^ 2 / 5 * ‖n‖ ^ 2 := by
  rw [← integral_indicator measurableSet_ball, integral_polar_actual]
  have he : (fun p : UnitSphere × Ioi (0 : ℝ) =>
      (Metric.ball (0 : Position) a).indicator (fun x => (inner ℝ n x) ^ 2) (p.2.1 • (p.1 : Position))) =
      (fun p => (inner ℝ n (p.1 : Position)) ^ 2 * (Iio a).indicator (fun t : ℝ => t ^ 2) p.2.1) := by
    funext p
    have hr : 0 < p.2.1 := mem_Ioi.mp p.2.2
    by_cases hpa : p.2.1 < a <;>
      simp [indicator, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, inner_smul_right, hpa]
    ring
  rw [he]
  have hprod := integral_prod_mul (μ := sphereArea) (ν := Measure.volumeIoiPow 2)
    (fun u : UnitSphere => (inner ℝ n (u : Position)) ^ 2)
    (fun r : Ioi (0 : ℝ) => (Iio a).indicator (fun t : ℝ => t ^ 2) r.1)
  rw [hprod, sphere_real_inner_square, radial_second_moment a ha,
    volume_real_ball_three a ha.le]
  ring

theorem ball_zero_inner_mean (a : ℝ) (n : Position) :
    (∫ x in Metric.ball (0 : Position) a, inner ℝ n x) = 0 := by
  let f : Position → ℝ := (Metric.ball (0 : Position) a).indicator (fun x => inner ℝ n x)
  have h := integral_neg_eq_self f (volume : Measure Position)
  have he : (fun x => f (-x)) = -f := by
    funext x
    by_cases hx : ‖x‖ < a <;> simp [f, indicator, Metric.mem_ball, dist_zero_right, hx]
  rw [he] at h
  change (∫ x, -f x) = ∫ x, f x at h
  rw [integral_neg] at h
  have hf : (∫ x, f x) = 0 := by linarith
  simpa only [f, integral_indicator measurableSet_ball] using hf

theorem ball_translate_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : Position) (a : ℝ) (f : Position → E) :
    (∫ x in Metric.ball c a, f (x - c)) = ∫ x in Metric.ball (0 : Position) a, f x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure Position))
    ((Metric.ball c a).indicator (fun x => f (x - c))) c
  have he : (fun x => (Metric.ball c a).indicator (fun y => f (y - c)) (x + c)) =
      (Metric.ball (0 : Position) a).indicator f := by
    funext x
    simp [indicator, Metric.mem_ball, dist_eq_norm]
  rw [he, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at h
  exact h.symm

theorem ball_volume (c : Position) (a : ℝ) (ha : 0 ≤ a) :
    volume.real (Metric.ball c a) = 4 * Real.pi / 3 * a ^ 3 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem ball_inner_square (c : Position) (a : ℝ) (ha : 0 < a) (n : Position) :
    (∫ x in Metric.ball c a, (inner ℝ n (x - c)) ^ 2) =
      volume.real (Metric.ball c a) * a ^ 2 / 5 * ‖n‖ ^ 2 := by
  calc
    _ = ∫ x in Metric.ball (0 : Position) a, (inner ℝ n x) ^ 2 :=
      ball_translate_integral c a (fun x => (inner ℝ n x) ^ 2)
    _ = _ := by rw [ball_zero_inner_square a ha n, ball_volume c a ha.le, volume_real_ball_three a ha.le]

theorem ball_inner_mean (c : Position) (a : ℝ) (n : Position) :
    (∫ x in Metric.ball c a, inner ℝ n (x - c)) = 0 := by
  rw [ball_translate_integral, ball_zero_inner_mean]

theorem ball_zero_norm_square (a : ℝ) (ha : 0 < a) :
    (∫ x in Metric.ball (0 : Position) a, ‖x‖ ^ 2) = 4 * Real.pi * a ^ 5 / 5 := by
  rw [← integral_indicator measurableSet_ball, integral_polar_actual]
  have he : (fun p : UnitSphere × Ioi (0 : ℝ) =>
      (Metric.ball (0 : Position) a).indicator (fun x => ‖x‖ ^ 2) (p.2.1 • (p.1 : Position))) =
      (fun p => (1 : ℝ) * (Iio a).indicator (fun t : ℝ => t ^ 2) p.2.1) := by
    funext p
    have hr : 0 < p.2.1 := mem_Ioi.mp p.2.2
    by_cases hpa : p.2.1 < a <;>
      simp [indicator, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hpa]
  rw [he]
  have hprod := integral_prod_mul (μ := sphereArea) (ν := Measure.volumeIoiPow 2)
    (fun _ : UnitSphere => (1 : ℝ))
    (fun r : Ioi (0 : ℝ) => (Iio a).indicator (fun t : ℝ => t ^ 2) r.1)
  rw [hprod, radial_second_moment a ha]
  simp only [integral_const, smul_eq_mul, mul_one, sphereArea_real_univ]
  ring

theorem ball_norm_square (c : Position) (a : ℝ) (ha : 0 < a) :
    (∫ x in Metric.ball c a, ‖x - c‖ ^ 2) = 3 * volume.real (Metric.ball c a) * a ^ 2 / 5 := by
  calc
    _ = ∫ x in Metric.ball (0 : Position) a, ‖x‖ ^ 2 := ball_translate_integral c a (fun x => ‖x‖ ^ 2)
    _ = _ := by rw [ball_zero_norm_square a ha, ball_volume c a ha.le]; ring

theorem weighted_current_norm_integral (c : Position) (a : ℝ) (ha : 0 < a)
    (p : DomainL2 (Metric.ball c a)) :
    (∫ x in Metric.ball c a, ‖x - c‖ * ‖(p : VectorL2) x‖) ≤
      Real.sqrt (3 * volume.real (Metric.ball c a) * a ^ 2 / 5) * ‖p‖ := by
  let D := Metric.ball c a
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa [D] using (ball_measure_ne_top c a).lt_top⟩
  have hg0 : MemLp (fun x : Position => ‖x - c‖) 2 (volume.restrict D) := by
    apply MemLp.of_bound (by fun_prop) a
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Metric.mem_ball, dist_eq_norm] using hx.le
  have hg := (memLp_indicator_iff_restrict (show MeasurableSet D from measurableSet_ball)).mpr hg0
  let g : Lp ℝ 2 volume := hg.toLp (D.indicator (fun x : Position => ‖x - c‖))
  let q : Lp ℝ 2 volume := ((Lp.memLp (p : VectorL2)).norm).toLp (fun x => ‖(p : VectorL2) x‖)
  have hqn : ‖q‖ = ‖p‖ := by
    change ‖q‖ = ‖(p : VectorL2)‖
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm _ (Lp.aestronglyMeasurable (p : VectorL2))]
  have hgn : ‖g‖ ^ 2 = 3 * volume.real (Metric.ball c a) * a ^ 2 / 5 := by
    have hs : inner ℝ g g = ‖g‖ ^ 2 := by simp [inner_self_eq_norm_sq_to_K]
    rw [← hs, L2.inner_def]
    calc
      _ = ∫ x in Metric.ball c a, ‖x - c‖ ^ 2 := by
        rw [← integral_indicator measurableSet_ball]
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp] with x hx
        change inner ℝ (g x) (g x) = _
        change g x = _ at hx
        rw [hx]
        by_cases hxs : x ∈ Metric.ball c a <;> simp [D, hxs, pow_two]
      _ = _ := ball_norm_square c a ha
  have hgn' : ‖g‖ = Real.sqrt (3 * volume.real (Metric.ball c a) * a ^ 2 / 5) := by
    rw [← hgn, Real.sqrt_sq (norm_nonneg g)]
  have hi : inner ℝ g q = ∫ x in Metric.ball c a, ‖x - c‖ * ‖(p : VectorL2) x‖ := by
    rw [L2.inner_def, ← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, ((Lp.memLp (p : VectorL2)).norm).coeFn_toLp] with x hx hq
    change inner ℝ (g x) (q x) = _
    change g x = _ at hx
    change q x = _ at hq
    rw [hx, hq]
    by_cases hxs : x ∈ Metric.ball c a <;> simp [D, hxs, RCLike.inner_apply, mul_comm]
  have hbound := real_inner_le_norm g q
  simpa only [hi, hgn', hqn] using hbound

theorem centered_bound (c : Position) (a : ℝ) (n : Position) :
    ∀ᵐ x ∂volume.restrict (Metric.ball c a), |inner ℝ n (x - c)| ≤ a * ‖n‖ := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx' : ‖x - c‖ < a := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  apply (abs_real_inner_le_norm n (x - c)).trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx'.le (norm_nonneg n)

def oddSource (c : Position) (a : ℝ) (n : Position) (e : Vector) : DomainL2 (Metric.ball c a) :=
  SourceTaylor.scalarSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a)
    (fun x => inner ℝ n (x - c)) (by fun_prop) (a * ‖n‖) (centered_bound c a n) e

theorem oddSource_coe (c : Position) (a : ℝ) (n : Position) (e : Vector) :
    (oddSource c a n e : VectorL2) =ᵐ[volume]
      (Metric.ball c a).indicator (fun x => ((inner ℝ n (x - c) : ℝ) : ℂ) • e) :=
  SourceTaylor.scalarSource_coe (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a)
    _ _ _ _ _

theorem oddSource_integral (c : Position) (a : ℝ) (n : Position) (e : Vector) :
    (∫ x, (oddSource c a n e : VectorL2) x) = 0 := by
  calc
    _ = ∫ x in Metric.ball c a, ((inner ℝ n (x - c) : ℝ) : ℂ) • e := by
      rw [← integral_indicator measurableSet_ball]
      exact integral_congr_ae (oddSource_coe c a n e)
    _ = (∫ x in Metric.ball c a, ((inner ℝ n (x - c) : ℝ) : ℂ)) • e := integral_smul_const _ _
    _ = 0 := by rw [integral_complex_ofReal, ball_inner_mean]; simp

theorem oddSource_norm_sq (c : Position) (a : ℝ) (ha : 0 < a) (n : Position) (e : Vector) :
    ‖oddSource c a n e‖ ^ 2 = volume.real (Metric.ball c a) * a ^ 2 / 5 * ‖n‖ ^ 2 * ‖e‖ ^ 2 := by
  change ‖(oddSource c a n e : VectorL2)‖ ^ 2 = _
  rw [← lp_integral_norm_sq volume]
  calc
    _ = ∫ x in Metric.ball c a, (inner ℝ n (x - c)) ^ 2 * ‖e‖ ^ 2 := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      filter_upwards [oddSource_coe c a n e] with x hx
      rw [hx]
      by_cases hxs : x ∈ Metric.ball c a <;>
        simp [hxs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ = (∫ x in Metric.ball c a, (inner ℝ n (x - c)) ^ 2) * ‖e‖ ^ 2 := integral_mul_const _ _
    _ = _ := by rw [ball_inner_square c a ha n]

theorem oddSource_norm (c : Position) (a : ℝ) (ha : 0 < a) (n : Position) (e : Vector) :
    ‖oddSource c a n e‖ = a * Real.sqrt (volume.real (Metric.ball c a) / 5) * ‖n‖ * ‖e‖ := by
  have hV : 0 ≤ volume.real (Metric.ball c a) / 5 := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [oddSource_norm_sq c a ha n e]
  calc
    _ = (a ^ 2 * (volume.real (Metric.ball c a) / 5)) * ‖n‖ ^ 2 * ‖e‖ ^ 2 := by ring
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hV]

theorem oddResponse_norm (c : Position) (a : ℝ) (ha : 0 < a) (n : Position) (e : Vector)
    (A : DomainL2 (Metric.ball c a) →L[ℂ] DomainL2 (Metric.ball c a)) {μ : ℝ} (hA : ‖A‖ ≤ μ) :
    ‖A (oddSource c a n e)‖ ≤ μ * (a * Real.sqrt (volume.real (Metric.ball c a) / 5) * ‖n‖ * ‖e‖) := by
  apply (A.le_opNorm _).trans
  rw [oddSource_norm c a ha n e]
  exact mul_le_mul_of_nonneg_right hA (by positivity)

theorem weighted_current_from_norm_bound (c : Position) (a : ℝ) (ha : 0 < a)
    (p : DomainL2 (Metric.ball c a)) {μ : ℝ} (_hμ : 0 ≤ μ)
    (hp : ‖p‖ ≤ μ * a * Real.sqrt (volume.real (Metric.ball c a) / 5)) :
    (∫ x in Metric.ball c a, ‖x - c‖ * ‖(p : VectorL2) x‖) ≤
      μ * (Real.sqrt 3 / 5) * a ^ 2 * volume.real (Metric.ball c a) := by
  have hV : 0 ≤ volume.real (Metric.ball c a) / 5 := by positivity
  have hrad : Real.sqrt (3 * volume.real (Metric.ball c a) * a ^ 2 / 5) =
      Real.sqrt 3 * a * Real.sqrt (volume.real (Metric.ball c a) / 5) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hV]
    ring
  calc
    _ ≤ Real.sqrt (3 * volume.real (Metric.ball c a) * a ^ 2 / 5) * ‖p‖ :=
      weighted_current_norm_integral c a ha p
    _ ≤ Real.sqrt (3 * volume.real (Metric.ball c a) * a ^ 2 / 5) *
        (μ * a * Real.sqrt (volume.real (Metric.ball c a) / 5)) :=
      mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
    _ = _ := by
      rw [hrad]
      calc
        _ = μ * Real.sqrt 3 * a ^ 2 * (Real.sqrt (volume.real (Metric.ball c a) / 5)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hV]; ring

theorem affineSource_decomposition (c : Position) (a : ℝ) (n : UnitSphere) (e : Vector)
    (R : ℝ) (hsub : Metric.ball c a ⊆ Metric.closedBall (0 : Position) R) :
    SourceTaylor.momentSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) n e R hsub =
      (((inner ℝ (n : Position) c : ℝ) : ℂ)) •
        SourceTaylor.constantSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) e +
        oddSource c a (n : Position) e := by
  let b := SourceTaylor.constantSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) e
  let z : ℂ := ((inner ℝ (n : Position) c : ℝ) : ℂ)
  let q := oddSource c a (n : Position) e
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [SourceTaylor.momentSource_coe (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) n e R hsub,
    SourceTaylor.constantSource_coe (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) e,
    oddSource_coe c a (n : Position) e, Lp.coeFn_smul z (b : VectorL2),
    Lp.coeFn_add (z • (b : VectorL2)) (q : VectorL2)] with x hs hb hq hz ha
  change (SourceTaylor.momentSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) n e R hsub : VectorL2) x =
    (z • (b : VectorL2) + (q : VectorL2)) x
  rw [hs, ha]
  change _ = (z • (b : VectorL2)) x + (q : VectorL2) x
  rw [hz]
  change _ = z • (b : VectorL2) x + (q : VectorL2) x
  rw [hb, hq]
  by_cases hx : x ∈ Metric.ball c a
  · simp only [indicator_of_mem hx]
    dsimp [z]
    rw [inner_sub_right, sub_smul]
    abel
  · simp only [indicator_of_notMem hx, smul_zero, add_zero]

end QuarticMaxwell.BallAffineMoments
