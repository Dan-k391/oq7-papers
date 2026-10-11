import PrescribedExtinction.FarFieldPhase
import PrescribedExtinction.ExteriorOutgoing

noncomputable section
set_option maxHeartbeats 1000000
namespace OQ7Prescribed

theorem transverseProjection_cross (n : Position) (hn : ‖n‖ = 1) (v : Vector) :
    transverseProjection n v = cross (cross (complexify n) v) (complexify n) := by
  rw [cross_cross, bilinear_complexify_self, hn]
  simp only [one_pow, Complex.ofReal_one, one_smul]
  change v - (∑ i, (n i : ℂ) * v i) • complexify n =
    v - bilinear v (complexify n) • complexify n
  have hb : bilinear v (complexify n) = ∑ i, (n i : ℂ) * v i := by
    simp only [bilinear, complexify, mul_comm]
  rw [hb]

theorem transverseProjection_norm_le (n : Position) (hn : ‖n‖ = 1) (v : Vector) :
    ‖transverseProjection n v‖ ≤ ‖v‖ := by
  rw [transverseProjection_cross n hn]
  have hnc : ‖complexify n‖ = 1 := by rw [complexify_norm, hn]
  apply (cross_norm_le _ _).trans
  simpa only [hnc, mul_one, one_mul] using cross_norm_le (complexify n) v

theorem kernelMagnetic_leading (k : ℝ) (x : Position) (hx : x ≠ 0) (v : Vector) :
    kernelMagnetic k x v =
      (((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x‖) • cross (complexify (radialDirection x)) v +
      (Complex.I * (k : ℂ) * outgoingRadial k ‖x‖ / (‖x‖ : ℂ)) •
        cross (complexify (radialDirection x)) v := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hc : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  ext i
  fin_cases i <;> simp [kernelMagnetic, cross, complexify, radialDirection, outgoingRadial,
    outgoingRadialFirst, PiLp.smul_apply, PiLp.add_apply, Complex.ofReal_pow, Complex.ofReal_inv]
  all_goals
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem cross_smul_left (a : ℂ) (u v : Vector) : cross (a • u) v = a • cross u v := by
  ext i
  fin_cases i <;> simp [cross, PiLp.smul_apply] <;> ring

theorem cross_add_left (u v w : Vector) : cross (u + v) w = cross u w + cross v w := by
  ext i
  fin_cases i <;> simp [cross, PiLp.add_apply] <;> ring

theorem cross_sub_left (u v w : Vector) : cross (u - v) w = cross u w - cross v w := by
  ext i
  fin_cases i <;> simp [cross, PiLp.sub_apply] <;> ring

theorem transverseProjection_difference_le (m n : Position) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1) (v : Vector) :
    ‖transverseProjection m v - transverseProjection n v‖ ≤ 2 * ‖m - n‖ * ‖v‖ := by
  have he : transverseProjection m v - transverseProjection n v =
      cross (cross (complexify (m - n)) v) (complexify m) +
        cross (cross (complexify n) v) (complexify (m - n)) := by
    rw [transverseProjection_cross m hm, transverseProjection_cross n hn, complexify_sub,
      cross_sub_left, cross_sub_left, cross_sub_right]
    abel
  rw [he]
  calc
    _ ≤ ‖cross (cross (complexify (m - n)) v) (complexify m)‖ +
        ‖cross (cross (complexify n) v) (complexify (m - n))‖ := norm_add_le _ _
    _ ≤ (‖complexify (m - n)‖ * ‖v‖) * ‖complexify m‖ +
        (‖complexify n‖ * ‖v‖) * ‖complexify (m - n)‖ := by
      apply add_le_add <;> apply (cross_norm_le _ _).trans <;>
        apply mul_le_mul_of_nonneg_right (cross_norm_le _ _) (norm_nonneg _)
    _ = _ := by rw [complexify_norm, complexify_norm, complexify_norm, hm, hn]; ring

def farFieldLowerConstant (k : ℝ) : ℝ := (3 * |k| + 4) / (4 * Real.pi)

theorem classicalDyadic_leading_error (k : ℝ) (x : Position) (hx : 1 ≤ ‖x‖) (v : Vector) :
    ‖classicalDyadic k x v -
      (((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x‖) • transverseProjection (radialDirection x) v‖ ≤
      farFieldLowerConstant k / ‖x‖ ^ 2 * ‖v‖ := by
  have hxn : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn := radialDirection_norm x hxn
  have hg : ‖outgoingRadial k ‖x‖‖ = 1 / (4 * Real.pi * ‖x‖) := by
    rw [← outgoingGreen_eq_radial, outgoingGreen_norm, one_div]
  have he : cross (kernelMagnetic k x v) (complexify (radialDirection x)) =
      (((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x‖) • transverseProjection (radialDirection x) v +
      (Complex.I * (k : ℂ) * outgoingRadial k ‖x‖ / (‖x‖ : ℂ)) •
        transverseProjection (radialDirection x) v := by
    rw [kernelMagnetic_leading k x hxn, cross_add_left, cross_smul_left, cross_smul_left,
      ← transverseProjection_cross _ hn]
  have hl : ‖(Complex.I * (k : ℂ) * outgoingRadial k ‖x‖ / (‖x‖ : ℂ)) •
      transverseProjection (radialDirection x) v‖ ≤ |k| / (4 * Real.pi * ‖x‖ ^ 2) * ‖v‖ := by
    rw [norm_smul]
    have hs : ‖Complex.I * (k : ℂ) * outgoingRadial k ‖x‖ / (‖x‖ : ℂ)‖ =
        |k| / (4 * Real.pi * ‖x‖ ^ 2) := by
      simp only [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, one_mul, hg]
      field_simp <;> ring
    rw [hs]
    exact mul_le_mul_of_nonneg_left (transverseProjection_norm_le _ hn v) (by positivity)
  calc
    _ ≤ ‖classicalDyadic k x v - cross (kernelMagnetic k x v) (complexify (radialDirection x))‖ +
        ‖cross (kernelMagnetic k x v) (complexify (radialDirection x)) -
          (((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x‖) • transverseProjection (radialDirection x) v‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 * |k| / (4 * Real.pi * ‖x‖ ^ 2) + 1 / (Real.pi * ‖x‖ ^ 3)) * ‖v‖ +
        |k| / (4 * Real.pi * ‖x‖ ^ 2) * ‖v‖ := by
      apply add_le_add
      · rw [norm_sub_rev]
        exact kernel_radiation_defect_norm_le k x hxn v
      · rw [he, add_sub_cancel_left]
        exact hl
    _ ≤ (2 * |k| / (4 * Real.pi * ‖x‖ ^ 2) + 1 / (Real.pi * ‖x‖ ^ 2)) * ‖v‖ +
        |k| / (4 * Real.pi * ‖x‖ ^ 2) * ‖v‖ := by
      gcongr
      nlinarith [sq_nonneg ‖x‖]
    _ = _ := by unfold farFieldLowerConstant; field_simp; ring

def farFieldKernelConstant (k R : ℝ) : ℝ :=
  4 * farFieldLowerConstant k + (k ^ 2 / (4 * Real.pi)) * (10 * R + |k| * R ^ 2)

theorem scaledOutgoingRadial (k : ℝ) (x y : Position) :
    ((‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))) *
      (((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x - y‖) =
      ((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) * scaledOutgoingPhase k x y := by
  have he : Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (k : ℂ) * (‖x - y‖ : ℂ)) =
      Complex.exp (Complex.I * ((k * (‖x - y‖ - ‖x‖) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold outgoingRadial scaledOutgoingPhase
  push_cast
  calc
    _ = ((k ^ 2 : ℝ) : ℂ) * (‖x‖ : ℂ) /
      (((4 * Real.pi : ℝ) : ℂ) * (‖x - y‖ : ℂ)) *
      (Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (k : ℂ) * (‖x - y‖ : ℂ))) := by push_cast; ring
    _ = _ := by rw [he]; push_cast; ring

/-- Uniform leading dyadic far field at every observation direction and every source point.
The error is a genuine kernel estimate, not a far-field hypothesis. -/
theorem displaced_dyadic_farField_error (k R : ℝ) (hR : 0 ≤ R)
    (x y : Position) (hx : 2 * R + 2 ≤ ‖x‖) (hy : ‖y‖ ≤ R) (v : Vector) :
    ‖((‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))) •
        classicalDyadic k (x - y) v -
      (((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((k * inner ℝ (radialDirection x) y : ℝ) : ℂ))) •
          transverseProjection (radialDirection x) v‖ ≤
      farFieldKernelConstant k R / ‖x‖ * ‖v‖ := by
  have hr : 0 < ‖x‖ := by linarith
  have hd : 1 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
  have hhalf : ‖x‖ / 2 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
  have hx0 : x ≠ 0 := norm_pos_iff.mp hr
  have hxy0 : x - y ≠ 0 := norm_pos_iff.mp (by linarith)
  let a : ℂ := (‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))
  let c : ℂ := ((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x - y‖
  let bcoef : ℂ := ((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ)
  let S := scaledOutgoingPhase k x y
  let q := Complex.exp (-Complex.I * ((k * inner ℝ (radialDirection x) y : ℝ) : ℂ))
  let m := radialDirection (x - y)
  let n := radialDirection x
  have hmn : ‖m - n‖ ≤ 4 * R / ‖x‖ := by
    apply (radialDirection_sub_norm_le_distance x y (by linarith)).trans
    calc
      _ ≤ 2 * R / (‖x‖ / 2) := by gcongr
      _ = _ := by ring
  have hproj : ‖transverseProjection m v - transverseProjection n v‖ ≤
      8 * R / ‖x‖ * ‖v‖ := by
    apply (transverseProjection_difference_le m n (radialDirection_norm _ hxy0) (radialDirection_norm _ hx0) v).trans
    calc
      _ ≤ 2 * (4 * R / ‖x‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hscaled : ‖S • transverseProjection m v - q • transverseProjection n v‖ ≤
      (10 * R + |k| * R ^ 2) / ‖x‖ * ‖v‖ := by
    have hsplit : S • transverseProjection m v - q • transverseProjection n v =
        (S - q) • transverseProjection m v + q • (transverseProjection m v - transverseProjection n v) := by
      simp only [sub_smul, smul_sub]
      abel
    rw [hsplit]
    calc
      _ ≤ ‖(S - q) • transverseProjection m v‖ +
          ‖q • (transverseProjection m v - transverseProjection n v)‖ := norm_add_le _ _
      _ ≤ ((2 * R + |k| * R ^ 2) / ‖x‖) * ‖v‖ + 8 * R / ‖x‖ * ‖v‖ := by
        rw [norm_smul, norm_smul, show ‖q‖ = 1 by dsimp [q]; simp [Complex.norm_exp], one_mul]
        exact add_le_add (mul_le_mul (scaledOutgoingPhase_plane_error k R hR x y hx hy)
          (transverseProjection_norm_le m (radialDirection_norm _ hxy0) v) (norm_nonneg _)
          (by positivity)) hproj
      _ = _ := by ring
  have ha : ‖a‖ = ‖x‖ := by dsimp [a]; simp [Complex.norm_exp]
  have hbcoef : ‖bcoef‖ = k ^ 2 / (4 * Real.pi) := by
    dsimp [bcoef]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hac : a * c = bcoef * S := scaledOutgoingRadial k x y
  change ‖a • classicalDyadic k (x - y) v - (bcoef * q) • transverseProjection n v‖ ≤ _
  calc
    _ ≤ ‖a • classicalDyadic k (x - y) v - a • (c • transverseProjection m v)‖ +
        ‖a • (c • transverseProjection m v) - (bcoef * q) • transverseProjection n v‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖x‖ * ‖classicalDyadic k (x - y) v - c • transverseProjection m v‖ +
        ‖bcoef‖ * ‖S • transverseProjection m v - q • transverseProjection n v‖ := by
      rw [← smul_sub, norm_smul, ha, smul_smul, hac,
        mul_smul bcoef S, mul_smul bcoef q, ← smul_sub, norm_smul]
    _ ≤ ‖x‖ * (farFieldLowerConstant k / ‖x - y‖ ^ 2 * ‖v‖) +
        (k ^ 2 / (4 * Real.pi)) * ((10 * R + |k| * R ^ 2) / ‖x‖ * ‖v‖) := by
      rw [hbcoef]
      exact add_le_add (mul_le_mul_of_nonneg_left (classicalDyadic_leading_error k (x - y) hd v) hr.le)
        (mul_le_mul_of_nonneg_left hscaled (by positivity))
    _ ≤ ‖x‖ * (farFieldLowerConstant k / (‖x‖ / 2) ^ 2 * ‖v‖) +
        (k ^ 2 / (4 * Real.pi)) * ((10 * R + |k| * R ^ 2) / ‖x‖ * ‖v‖) := by
      gcongr
      unfold farFieldLowerConstant
      positivity
    _ = _ := by unfold farFieldKernelConstant; field_simp; ring

end OQ7Prescribed
