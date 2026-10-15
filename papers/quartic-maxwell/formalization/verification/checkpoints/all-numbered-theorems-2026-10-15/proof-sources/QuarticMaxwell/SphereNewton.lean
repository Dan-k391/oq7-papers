import PrescribedExtinction.SphericalProduct
import PrescribedExtinction.SphericalAngular
import QuarticMaxwell.SharpVolume
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Actual Newtonian sphere potential foundations. The shell primitive is
proved by real differentiation and integration; no static response or desired
ball eigenvalue is imposed as a hypothesis. -/
noncomputable section
namespace QuarticMaxwell
namespace SphereNewton
open OQ7Prescribed MeasureTheory Set
open scoped Interval

def shellRadicand (r s θ : ℝ) : ℝ := r ^ 2 + s ^ 2 - 2 * r * s * Real.cos θ
def shellIntegrand (r s θ : ℝ) : ℝ := Real.sin θ / Real.sqrt (shellRadicand r s θ)
def shellPrimitive (r s θ : ℝ) : ℝ := Real.sqrt (shellRadicand r s θ) / (r * s)

theorem shellRadicand_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) (θ : ℝ) :
    0 < shellRadicand r s θ := by
  have hgap := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hcos := mul_nonneg (mul_nonneg hr.le hs.le) (sub_nonneg.mpr (Real.cos_le_one θ))
  unfold shellRadicand
  nlinarith

theorem shellPrimitive_derivative {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) (θ : ℝ) :
    HasDerivAt (shellPrimitive r s) (shellIntegrand r s θ) θ := by
  have hrad := shellRadicand_pos hr hs hne θ
  have hd : HasDerivAt (shellRadicand r s) (2 * r * s * Real.sin θ) θ := by
    convert (hasDerivAt_const θ (r ^ 2 + s ^ 2)).sub ((Real.hasDerivAt_cos θ).const_mul (2 * r * s)) using 1
    · rfl
    · ring
  convert (hd.sqrt hrad.ne').div_const (r * s) using 1
  · rfl
  · unfold shellIntegrand
    field_simp [hr.ne', hs.ne', (Real.sqrt_pos.mpr hrad).ne']

theorem shellIntegrand_continuous {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) :
    Continuous (shellIntegrand r s) := by
  unfold shellIntegrand
  apply Continuous.div Real.continuous_sin
  · unfold shellRadicand
    fun_prop
  · intro θ
    exact (Real.sqrt_pos.mpr (shellRadicand_pos hr hs hne θ)).ne'

/-- The exact non-singular spherical-shell angular Newton integral. The single
radius r=s is irrelevant to radial Lebesgue integration and is not assumed. -/
theorem angular_shell_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) :
    (∫ θ in (0 : ℝ)..Real.pi, shellIntegrand r s θ) =
      (r + s - |r - s|) / (r * s) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => shellPrimitive_derivative hr hs hne θ)
    ((shellIntegrand_continuous hr hs hne).intervalIntegrable 0 Real.pi)
  rw [h]
  have h0 : shellRadicand r s 0 = (r - s) ^ 2 := by simp [shellRadicand]; ring
  have hpi : shellRadicand r s Real.pi = (r + s) ^ 2 := by simp [shellRadicand]; ring
  unfold shellPrimitive
  rw [h0, hpi, Real.sqrt_sq (by linarith : 0 ≤ r + s), Real.sqrt_sq_eq_abs]
  ring

theorem angular_shell_inner {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    (∫ θ in (0 : ℝ)..Real.pi, shellIntegrand r s θ) = 2 / s := by
  rw [angular_shell_integral hr (hr.trans hrs) (ne_of_lt hrs), abs_of_neg (sub_neg.mpr hrs)]
  field_simp
  ring

theorem angular_shell_outer {r s : ℝ} (hs : 0 < s) (hsr : s < r) :
    (∫ θ in (0 : ℝ)..Real.pi, shellIntegrand r s θ) = 2 / r := by
  rw [angular_shell_integral (hs.trans hsr) hs (ne_of_gt hsr), abs_of_pos (sub_pos.mpr hsr)]
  field_simp
  ring

theorem integrable_spherical_actual {f : OQ7Prescribed.Position → ℝ} (hf : Integrable f volume) :
    IntegrableOn (fun p : Fin 3 → ℝ => p 0 ^ 2 * Real.sin (p 1) *
      f (p 0 • sphereDirection (p 1) (p 2))) sphericalDomain volume := by
  have hv := (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_of_integrable hf
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    sphericalDomain_measurableSet (fun p _ => (sphericalPoint_hasFDerivAt p).hasFDerivWithinAt)
    sphericalPoint_injOn (fun x : Fin 3 → ℝ => f (WithLp.toLp 2 x))).mp hv.integrableOn
  apply hi.congr_fun _ sphericalDomain_measurableSet
  intro p hp
  simp only [smul_eq_mul, sphericalDerivative_det, sphericalPoint_toLp]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
    (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1).le)]

theorem spherical_integral_iterated {f : OQ7Prescribed.Position → ℝ} (hf : Integrable f volume) :
    (∫ x, f x) = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi,
      ∫ φ in Ioo (-Real.pi) Real.pi,
        r ^ 2 * Real.sin θ * f (r • sphereDirection θ φ) := by
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    p.1 ^ 2 * Real.sin p.2.1 * f (p.1 • sphereDirection p.2.1 p.2.2)
  have hi : IntegrableOn G (Ioi (0 : ℝ) ×ˢ (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi)) volume := by
    apply (sphericalTripleEquiv_measurePreserving.integrableOn_comp_preimage
      sphericalTripleEquiv.measurableEmbedding).mp
    rw [sphericalTripleEquiv_domain]
    exact integrable_spherical_actual hf
  have hi' : IntegrableOn G (Ioi (0 : ℝ) ×ˢ (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi))
      (volume.prod volume) := by simpa only [Measure.volume_eq_prod] using hi
  rw [integral_spherical_actual]
  have heq : (∫ p in sphericalDomain, p 0 ^ 2 * Real.sin (p 1) *
      f (WithLp.toLp 2 (sphericalPoint p))) =
      ∫ p in sphericalDomain, G (p 0, (p 1, p 2)) := by
    simp only [G, sphericalPoint_toLp]
  rw [heq, sphericalDomain_product_integral, Measure.volume_eq_prod, setIntegral_prod G hi']
  have hprod : Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi))) := by
    simpa only [IntegrableOn, Measure.prod_restrict] using hi'
  apply integral_congr_ae
  filter_upwards [hprod.prod_right_ae] with r hr
  have hinner : IntegrableOn (fun p : ℝ × ℝ => G (r, p))
      (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod] using hr
  rw [Measure.volume_eq_prod, setIntegral_prod _ hinner]

theorem spherical_axis_distance (r s θ φ : ℝ) :
    ‖r • sphereDirection θ φ - s • basisR 2‖ = Real.sqrt (shellRadicand r s θ) := by
  have hnorm : ‖r • sphereDirection θ φ - s • basisR 2‖ ^ 2 = shellRadicand r s θ := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply, sphereDirection, basisR,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, smul_eq_mul,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Pi.single_apply, Fin.reduceEq, ite_false, ite_true, mul_zero, mul_one, sub_zero]
    unfold shellRadicand
    linear_combination (r ^ 2 * Real.sin θ ^ 2) * Real.sin_sq_add_cos_sq φ +
      r ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]

def radialIntegrand (s r : ℝ) : ℝ := r ^ 2 / max r s
def radialPotential (a s : ℝ) : ℝ := ∫ r in (0 : ℝ)..a, radialIntegrand s r

theorem radialIntegrand_continuous {s : ℝ} (hs : 0 < s) : Continuous (radialIntegrand s) := by
  unfold radialIntegrand
  apply Continuous.div (by fun_prop) (continuous_id.max continuous_const)
  intro r
  exact ne_of_gt (hs.trans_le (le_max_right r s))

theorem radialPotential_exterior {a s : ℝ} (ha : 0 ≤ a) (_hs : 0 < s) (has : a ≤ s) :
    radialPotential a s = a ^ 3 / (3 * s) := by
  have heq : radialPotential a s = ∫ r in (0 : ℝ)..a, r ^ 2 / s := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 a := by simpa only [uIcc_of_le ha] using hr
    have hra : r ≤ a := hr'.2
    simp only [radialIntegrand, max_eq_right (hra.trans has)]
  rw [heq, intervalIntegral.integral_div, integral_pow]
  norm_num
  ring

theorem radialPotential_zero {a : ℝ} (ha : 0 ≤ a) : radialPotential a 0 = a ^ 2 / 2 := by
  have heq : radialPotential a 0 = ∫ r in (0 : ℝ)..a, r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 a := by simpa only [uIcc_of_le ha] using hr
    have hr0 : 0 ≤ r := hr'.1
    unfold radialIntegrand
    rw [max_eq_left hr0]
    by_cases hz : r = 0
    · simp only [hz, zero_pow (by norm_num : 2 ≠ 0), div_zero]
    · field_simp
  rw [heq, integral_id]
  ring

theorem radialPotential_interior {a s : ℝ} (hs0 : 0 ≤ s) (hsa : s ≤ a) :
    radialPotential a s = (3 * a ^ 2 - s ^ 2) / 6 := by
  by_cases hs : s = 0
  · subst s
    rw [radialPotential_zero hsa]
    ring
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hint := radialIntegrand_continuous hspos
  have hright : (∫ r in s..a, radialIntegrand s r) = (a ^ 2 - s ^ 2) / 2 := by
    have heq : (∫ r in s..a, radialIntegrand s r) = ∫ r in s..a, r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc s a := by simpa only [uIcc_of_le hsa] using hr
      have hsr : s ≤ r := hr'.1
      unfold radialIntegrand
      rw [max_eq_left hsr]
      field_simp [(hspos.trans_le hsr).ne']
    rw [heq, integral_id]
  have hleft := radialPotential_exterior hs0 hspos (le_refl s)
  unfold radialPotential at hleft ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint.intervalIntegrable 0 s)
    (hint.intervalIntegrable s a), hleft, hright]
  field_simp
  ring

theorem angular_shell_max {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) :
    (∫ θ in (0 : ℝ)..Real.pi, shellIntegrand r s θ) = 2 / max r s := by
  by_cases hrs : r ≤ s
  · rw [max_eq_right hrs]
    exact angular_shell_inner hr (lt_of_le_of_ne hrs hne)
  · rw [max_eq_left (le_of_not_ge hrs)]
    exact angular_shell_outer hs (lt_of_not_ge hrs)

theorem angular_set_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) :
    (∫ θ in Ioo (0 : ℝ) Real.pi, shellIntegrand r s θ) = 2 / max r s := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact angular_shell_max hr hs hne

theorem azimuth_constant_integral (c : ℝ) :
    (∫ _φ in Ioo (-Real.pi) Real.pi, c) = 2 * Real.pi * c := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

def ballNewtonPotential (a : ℝ) (x : OQ7Prescribed.Position) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ y in Metric.ball (0 : OQ7Prescribed.Position) a, ‖y - x‖⁻¹

/-- The actual three-dimensional ball-volume potential, evaluated on the
polar axis by the spherical change of variables and the proved shell integral. -/
theorem ballNewton_axis {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    ballNewtonPotential a (s • basisR 2) = radialPotential a s := by
  let f : OQ7Prescribed.Position → ℝ :=
    (Metric.ball 0 a).indicator (fun y => ‖y - s • basisR 2‖⁻¹)
  have hf : Integrable f volume :=
    (newton_bounded_support_integrable (Metric.ball 0 a) Metric.ball_subset_closedBall
      (s • basisR 2)).integrable_indicator measurableSet_ball
  have hpolar := spherical_integral_iterated hf
  have hradial : (∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi,
        ∫ φ in Ioo (-Real.pi) Real.pi, r ^ 2 * Real.sin θ * f (r • sphereDirection θ φ)) =
      ∫ r in Ioi (0 : ℝ), (Iio a).indicator (fun r => 4 * Real.pi * radialIntegrand s r) r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne s)] with r hr hne
    have hr0 : 0 < r := hr
    by_cases hra : r < a
    · have hfpoint (θ φ : ℝ) : r ^ 2 * Real.sin θ * f (r • sphereDirection θ φ) =
          r ^ 2 * shellIntegrand r s θ := by
        simp only [f, indicator_of_mem (show r • sphereDirection θ φ ∈ Metric.ball (0 : OQ7Prescribed.Position) a by
          simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos hr0, sphereDirection_norm, mul_one] using hra),
          spherical_axis_distance, shellIntegrand]
        ring
      simp_rw [hfpoint, azimuth_constant_integral]
      have hθ : (fun θ : ℝ => 2 * Real.pi * (r ^ 2 * shellIntegrand r s θ)) =
          (fun θ => (2 * Real.pi * r ^ 2) * shellIntegrand r s θ) := by funext θ; ring
      rw [hθ, integral_const_mul, angular_set_integral hr0 hs hne]
      simp [Set.indicator, hra, radialIntegrand]
      ring
    · have hfpoint (θ φ : ℝ) : r ^ 2 * Real.sin θ * f (r • sphereDirection θ φ) = 0 := by
        have hnot : r • sphereDirection θ φ ∉ Metric.ball (0 : OQ7Prescribed.Position) a := by
          simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos hr0, sphereDirection_norm, mul_one] using hra
        simp [f, hnot]
      simp [hfpoint, Set.indicator, hra]
  have hwhole : (∫ y in Metric.ball (0 : OQ7Prescribed.Position) a, ‖y - s • basisR 2‖⁻¹) =
      4 * Real.pi * radialPotential a s := by
    rw [← integral_indicator measurableSet_ball, hpolar, hradial,
      setIntegral_indicator measurableSet_Iio]
    have hset : Ioi (0 : ℝ) ∩ Iio a = Ioo (0 : ℝ) a := by ext r; simp
    rw [hset, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ha]
    rfl
  rw [ballNewtonPotential, hwhole]
  field_simp

theorem ballNewtonPotential_orthogonal (a : ℝ)
    (Q : OQ7Prescribed.Position ≃ₗᵢ[ℝ] OQ7Prescribed.Position) (x : OQ7Prescribed.Position) :
    ballNewtonPotential a (Q x) = ballNewtonPotential a x := by
  unfold ballNewtonPotential
  congr 1
  let f : OQ7Prescribed.Position → ℝ := fun y => ‖y - Q x‖⁻¹
  have h := Q.measurePreserving.setIntegral_preimage_emb Q.toMeasurableEquiv.measurableEmbedding
    f (Metric.ball (0 : OQ7Prescribed.Position) a)
  have hset : Q ⁻¹' Metric.ball (0 : OQ7Prescribed.Position) a =
      Metric.ball (0 : OQ7Prescribed.Position) a := by
    ext y
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, Q.norm_map]
  rw [hset] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  change ‖Q y - Q x‖⁻¹ = ‖y - x‖⁻¹
  rw [← Q.map_sub, Q.norm_map]

/-- Newton's actual solid-ball potential at every observation point, with no
sphere-response hypothesis or point-dipole model. -/
theorem ballNewton_radial {a : ℝ} (ha : 0 < a) (x : OQ7Prescribed.Position) :
    ballNewtonPotential a x = radialPotential a ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [ballNewtonPotential]
    simp only [sub_zero]
    rw [newton_ball_integral ha, norm_zero, radialPotential_zero ha.le]
    field_simp
    norm_num
  · have hb : ‖basisR 2‖ = 1 := by
      have hb2 : ‖basisR 2‖ ^ 2 = 1 := by
        simp [basisR]
      nlinarith [norm_nonneg (basisR 2)]
    have hnorm : ‖x‖ = ‖‖x‖ • basisR 2‖ := by
      rw [norm_smul, hb, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), mul_one]
    let Q := (ℝ ∙ (x - ‖x‖ • basisR 2))ᗮ.reflection
    have hQ : Q x = ‖x‖ • basisR 2 := Submodule.reflection_sub hnorm
    have h := ballNewtonPotential_orthogonal a Q x
    rw [hQ] at h
    exact h.symm.trans (ballNewton_axis ha.le (norm_pos_iff.mpr hx))

theorem ballNewton_interior {a : ℝ} (ha : 0 < a) (x : OQ7Prescribed.Position) (hx : ‖x‖ ≤ a) :
    ballNewtonPotential a x = (3 * a ^ 2 - ‖x‖ ^ 2) / 6 := by
  rw [ballNewton_radial ha]
  exact radialPotential_interior (norm_nonneg x) hx

theorem ballNewton_exterior {a : ℝ} (ha : 0 < a) (x : OQ7Prescribed.Position) (hx : a ≤ ‖x‖) :
    ballNewtonPotential a x = a ^ 3 / (3 * ‖x‖) := by
  rw [ballNewton_radial ha]
  exact radialPotential_exterior ha.le (ha.trans_le hx) hx

end SphereNewton
end QuarticMaxwell
