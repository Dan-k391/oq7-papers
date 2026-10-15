import QuarticMaxwell.Rearrangement
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact three-dimensional Newton-kernel integral on a ball, followed by
the same-volume measurable-support rearrangement. The operator Schur test is
separate from this scalar geometric estimate. -/

noncomputable section
namespace QuarticMaxwell
open Set MeasureTheory Metric

abbrev Position := EuclideanSpace ℝ (Fin 3)

def volumeRadius (V : ℝ) : ℝ := (3 * V / (4 * Real.pi)) ^ (1 / (3 : ℝ))

theorem volumeRadius_pos {V : ℝ} (hV : 0 < V) : 0 < volumeRadius V := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem volumeRadius_cube {V : ℝ} (hV : 0 ≤ V) :
    volumeRadius V ^ 3 = 3 * V / (4 * Real.pi) := by
  unfold volumeRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 3 * V / (4 * Real.pi))]
  norm_num

theorem volumeRadius_volume {V : ℝ} (hV : 0 ≤ V) :
    4 * Real.pi / 3 * volumeRadius V ^ 3 = V := by
  rw [volumeRadius_cube hV]
  field_simp

theorem volume_real_ball_three (a : ℝ) (ha : 0 ≤ a) :
    volume.real (ball (0 : Position) a) = 4 * Real.pi / 3 * a ^ 3 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem newton_ball_integrable (a : ℝ) :
    IntegrableOn (fun x : Position => ‖x‖⁻¹) (ball 0 a) volume := by
  rw [integrableOn_fun_norm_addHaar volume]
  have h : IntegrableOn (fun y : ℝ => y) (Ioo 0 a) volume :=
    continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  apply h.congr_fun _ measurableSet_Ioo
  intro y hy
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul]
  field_simp

theorem newton_ball_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in ball (0 : Position) a, ‖x‖⁻¹) = 2 * Real.pi * a ^ 2 := by
  let f : ℝ → ℝ := (Iio a).indicator (fun y => y⁻¹)
  have hf : (∫ x in ball (0 : Position) a, ‖x‖⁻¹) =
      ∫ x : Position, f ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext x
    simp [f, indicator, Metric.mem_ball, dist_zero_right]
  rw [hf, integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul]
  rw [volume_real_ball_three 1 (by norm_num)]
  have hrad : (∫ y in Ioi (0 : ℝ), y ^ 2 * f y) = ∫ y in Ioo (0 : ℝ) a, y := by
    have hind : (fun y : ℝ => y ^ 2 * f y) =
        (Iio a).indicator (fun y : ℝ => y ^ 2 * y⁻¹) := by
      funext y
      by_cases hy : y < a <;> simp [f, indicator, hy]
    rw [hind, setIntegral_indicator measurableSet_Iio]
    have hset : Ioi (0 : ℝ) ∩ Iio a = Ioo (0 : ℝ) a := by ext y; simp
    rw [hset]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    field_simp
  rw [hrad, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ha.le]
  norm_num
  ring

/-- Sharp measurable-support estimate, assuming the radius is chosen to match
the support volume. The integrability hypothesis is ordinary local integrability
of the Newton kernel; it does not encode the desired integral inequality. -/
theorem newton_same_volume_bound (s : Set Position) (hs : MeasurableSet s)
    (hsfin : volume s ≠ ⊤) {a : ℝ} (ha : 0 < a)
    (hvol : volume.real s = 4 * Real.pi / 3 * a ^ 3)
    (hint : IntegrableOn (fun x : Position => ‖x‖⁻¹) s volume) :
    (∫ x in s, ‖x‖⁻¹) ≤ 2 * Real.pi * a ^ 2 := by
  have hbfin : volume (ball (0 : Position) a) ≠ ⊤ := by
    exact ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Position) a).measure_lt_top).ne
  have hvol' : volume.real s = volume.real (ball (0 : Position) a) := by
    rw [volume_real_ball_three a ha.le]
    exact hvol
  have hin : ∀ᵐ x ∂(volume : Measure Position), x ∈ ball (0 : Position) a →
      a⁻¹ ≤ ‖x‖⁻¹ := by
    filter_upwards [volume.ae_ne (0 : Position)] with x hx
    intro hxa
    have hxn : x ≠ 0 := hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxn
    have hxa' : ‖x‖ < a := by simpa [Metric.mem_ball, dist_zero_right] using hxa
    exact (inv_le_inv₀ ha hnorm).mpr hxa'.le
  have hout : ∀ᵐ x ∂(volume : Measure Position), x ∉ ball (0 : Position) a →
      ‖x‖⁻¹ ≤ a⁻¹ := by
    filter_upwards with x
    intro hxa
    have hxa' : a ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_zero_right] using hxa
    exact (inv_le_inv₀ (ha.trans_le hxa') ha).mpr hxa'
  have h := threshold_rearrangement volume s (ball (0 : Position) a)
    hs measurableSet_ball hsfin hbfin hvol' (fun x : Position => ‖x‖⁻¹)
    hint (newton_ball_integrable a) a⁻¹ hin hout
  simpa only [newton_ball_integral ha] using h

theorem newton_ball_integrable_center (x : Position) (a : ℝ) :
    IntegrableOn (fun y : Position => ‖y - x‖⁻¹) (ball x a) volume := by
  rw [← integrable_indicator_iff measurableSet_ball]
  have hbase := (newton_ball_integrable a).integrable_indicator measurableSet_ball
  have htrans := (measurePreserving_sub_right (volume : Measure Position) x).integrable_comp_of_integrable hbase
  convert htrans using 1
  funext y
  simp [Function.comp_def, indicator, Metric.mem_ball, dist_eq_norm]

theorem newton_ball_integral_center (x : Position) {a : ℝ} (ha : 0 < a) :
    (∫ y in ball x a, ‖y - x‖⁻¹) = 2 * Real.pi * a ^ 2 := by
  have h := integral_add_right_eq_self (μ := (volume : Measure Position))
    ((ball x a).indicator (fun y : Position => ‖y - x‖⁻¹)) x
  have hfun : (fun y : Position => (ball x a).indicator
      (fun z : Position => ‖z - x‖⁻¹) (y + x)) =
      (ball (0 : Position) a).indicator (fun y : Position => ‖y‖⁻¹) := by
    funext y
    simp [indicator, Metric.mem_ball, dist_eq_norm]
  rw [hfun, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at h
  exact h.symm.trans (newton_ball_integral ha)

theorem newton_bounded_support_integrable (s : Set Position) {R : ℝ}
    (hsub : s ⊆ closedBall (0 : Position) R) (x : Position) :
    IntegrableOn (fun y : Position => ‖y - x‖⁻¹) s volume := by
  apply (newton_ball_integrable_center x (R + ‖x‖ + 1)).mono_set
  intro y hy
  have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hsub hy
  have hb := norm_sub_le y x
  simp only [Metric.mem_ball, dist_eq_norm]
  linarith

/-- The volume-only Newton-kernel bound is uniform over every observation
point and every measurable bounded support, including disconnected supports
with empty interior. `a` is the radius of its same-volume ball. -/
theorem newton_bounded_support_uniform (s : Set Position) (hs : MeasurableSet s)
    {R a : ℝ} (_hR : 0 ≤ R) (ha : 0 < a)
    (hsub : s ⊆ closedBall (0 : Position) R)
    (hvol : volume.real s = 4 * Real.pi / 3 * a ^ 3) (x : Position) :
    (∫ y in s, ‖x - y‖⁻¹) ≤ 2 * Real.pi * a ^ 2 := by
  have hsfin : volume s ≠ ⊤ :=
    ((measure_mono hsub).trans_lt (isCompact_closedBall (0 : Position) R).measure_lt_top).ne
  have hbfin : volume (ball x a) ≠ ⊤ := by
    exact ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall x a).measure_lt_top).ne
  have hvol' : volume.real s = volume.real (ball x a) := by
    rw [hvol]
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hint : IntegrableOn (fun y : Position => ‖y - x‖⁻¹) s volume := by
    apply (newton_ball_integrable_center x (R + ‖x‖ + 1)).mono_set
    intro y hy
    have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hsub hy
    have hb := norm_sub_le y x
    simp only [Metric.mem_ball, dist_eq_norm]
    linarith
  have hin : ∀ᵐ y ∂(volume : Measure Position), y ∈ ball x a →
      a⁻¹ ≤ ‖y - x‖⁻¹ := by
    filter_upwards [volume.ae_ne x] with y hy
    intro hya
    have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    have hya' : ‖y - x‖ < a := by simpa [Metric.mem_ball, dist_eq_norm] using hya
    exact (inv_le_inv₀ ha hnorm).mpr hya'.le
  have hout : ∀ᵐ y ∂(volume : Measure Position), y ∉ ball x a →
      ‖y - x‖⁻¹ ≤ a⁻¹ := by
    filter_upwards with y
    intro hya
    have hya' : a ≤ ‖y - x‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hya
    exact (inv_le_inv₀ (ha.trans_le hya') ha).mpr hya'
  have h := threshold_rearrangement volume s (ball x a)
    hs measurableSet_ball hsfin hbfin hvol' (fun y : Position => ‖y - x‖⁻¹)
    hint (newton_ball_integrable_center x a) a⁻¹ hin hout
  rw [newton_ball_integral_center x ha] at h
  simpa only [norm_sub_rev] using h

theorem measurable_support_newton_uniform (s : Set Position) (hs : MeasurableSet s)
    {R : ℝ} (hR : 0 ≤ R) (hsub : s ⊆ closedBall (0 : Position) R)
    (hV : 0 < volume.real s) (x : Position) :
    (∫ y in s, ‖x - y‖⁻¹) ≤ 2 * Real.pi * volumeRadius (volume.real s) ^ 2 := by
  exact newton_bounded_support_uniform s hs hR (volumeRadius_pos hV) hsub
    (volumeRadius_volume hV.le).symm x

end QuarticMaxwell
