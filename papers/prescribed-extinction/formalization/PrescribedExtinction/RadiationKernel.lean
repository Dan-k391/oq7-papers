import PrescribedExtinction.GreenGradient

/-! Actual dyadic and magnetic kernels, the exact Silver--Müller defect,
complex cross-product norms, and uniform displaced-source radiation bounds.
No exterior field identification or scattering solution is assumed. -/
noncomputable section
namespace OQ7Prescribed

theorem cross_cross (a b c : Vector) :
    cross (cross a b) c = bilinear a c • b - bilinear b c • a := by
  ext i
  fin_cases i <;> simp [cross, bilinear, Fin.sum_univ_three, PiLp.smul_apply, PiLp.sub_apply] <;> ring

set_option maxHeartbeats 1000000 in
theorem cross_squareNorm_identity (u v : Vector) :
    squareNorm (cross u v) + Complex.normSq (pairing u v) = squareNorm u * squareNorm v := by
  simp [squareNorm, cross, pairing, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem cross_norm_le (u v : Vector) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h := cross_squareNorm_identity u v
  rw [squareNorm_eq_norm_sq, squareNorm_eq_norm_sq, squareNorm_eq_norm_sq] at h
  nlinarith [Complex.normSq_nonneg (pairing u v), norm_nonneg (cross u v),
    norm_nonneg u, norm_nonneg v, mul_nonneg (norm_nonneg u) (norm_nonneg v)]

theorem cross_sub_right (u v w : Vector) : cross u (v - w) = cross u v - cross u w := by
  ext i
  fin_cases i <;> simp [cross, PiLp.sub_apply] <;> ring

theorem complexify_sub (x y : Position) : complexify (x - y) = complexify x - complexify y := by
  ext i
  simp [complexify, PiLp.sub_apply]

theorem complexify_norm (x : Position) : ‖complexify x‖ = ‖x‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (complexify_norm_sq x)

def radialDirection (x : Position) : Position := ‖x‖⁻¹ • x

theorem radialDirection_sub_norm_le_distance (x y : Position) (hxy : ‖y‖ < ‖x‖) :
    ‖radialDirection (x - y) - radialDirection x‖ ≤
      2 * ‖y‖ / ‖x - y‖ := by
  have hr : 0 < ‖x‖ := (norm_nonneg y).trans_lt hxy
  have hs : 0 < ‖x - y‖ := by
    have hb := norm_sub_norm_le x y
    linarith
  have hdiff : |‖x‖ - ‖x - y‖| ≤ ‖y‖ := by
    simpa using abs_norm_sub_norm_le x (x - y)
  have he : radialDirection (x - y) - radialDirection x =
      (‖x - y‖⁻¹ - ‖x‖⁻¹) • x - ‖x - y‖⁻¹ • y := by
    simp [radialDirection, smul_sub, sub_smul]
    abel
  have ht : ‖(‖x - y‖⁻¹ - ‖x‖⁻¹) • x‖ =
      |‖x‖ - ‖x - y‖| / ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    rw [show ‖x - y‖⁻¹ - ‖x‖⁻¹ = (‖x‖ - ‖x - y‖) / (‖x - y‖ * ‖x‖) by field_simp]
    rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos hr]
    field_simp
  rw [he]
  calc
    _ ≤ ‖(‖x - y‖⁻¹ - ‖x‖⁻¹) • x‖ + ‖‖x - y‖⁻¹ • y‖ := norm_sub_le _ _
    _ = |‖x‖ - ‖x - y‖| / ‖x - y‖ + ‖y‖ / ‖x - y‖ := by
      rw [ht, norm_smul]
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ ‖y‖ / ‖x - y‖ + ‖y‖ / ‖x - y‖ := by gcongr
    _ = 2 * ‖y‖ / ‖x - y‖ := by ring

theorem radialDirection_sub_norm_le (x y : Position) (hxy : ‖y‖ < ‖x‖) :
    ‖radialDirection (x - y) - radialDirection x‖ ≤
      2 * ‖y‖ / (‖x‖ - ‖y‖) := by
  apply (radialDirection_sub_norm_le_distance x y hxy).trans
  apply div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hxy)
  exact norm_sub_norm_le x y

theorem bilinear_complexify_self (x : Position) :
    bilinear (complexify x) (complexify x) = (‖x‖ ^ 2 : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [bilinear, complexify, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
  ring

theorem bilinear_complexify_eq_inner (x : Position) (v : Vector) :
    bilinear (complexify x) v = inner ℂ (complexify x) v := by
  simp [bilinear, complexify, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem bilinear_radial_smul_norm_le (x : Position) (v : Vector) :
    ‖bilinear (complexify x) v • complexify x‖ ≤ ‖x‖ ^ 2 * ‖v‖ := by
  rw [bilinear_complexify_eq_inner]
  have h := (InnerProductSpace.rankOne ℂ (complexify x) (complexify x)).le_opNorm v
  simpa [InnerProductSpace.rankOne_apply, InnerProductSpace.norm_rankOne,
    ← sq, complexify_norm_sq] using h

def kernelMagnetic (k : ℝ) (x : Position) (v : Vector) : Vector :=
  (-Complex.I * (k : ℂ) * outgoingRadialFirst k ‖x‖ / (‖x‖ : ℂ)) • cross (complexify x) v

theorem kernelMagnetic_gradient (k : ℝ) (x : Position) (v : Vector) :
    kernelMagnetic k x v = (-Complex.I * (k : ℂ)) •
      WithLp.toLp 2 ![outgoingGradient k 1 x * v 2 - outgoingGradient k 2 x * v 1,
        outgoingGradient k 2 x * v 0 - outgoingGradient k 0 x * v 2,
        outgoingGradient k 0 x * v 1 - outgoingGradient k 1 x * v 0] := by
  ext i
  fin_cases i <;> simp [kernelMagnetic, cross, complexify, outgoingGradient,
    PiLp.smul_apply, Complex.real_smul, div_eq_mul_inv] <;> ring

theorem kernelMagnetic_norm_le (k : ℝ) (x : Position) (hx : x ≠ 0) (v : Vector) :
    ‖kernelMagnetic k x v‖ ≤
      (|k| * (|k| * ‖x‖ + 1) / (4 * Real.pi * ‖x‖ ^ 2)) * ‖v‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  have hp : ‖Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 1‖ ≤ |k| * ‖x‖ + 1 := by
    simpa [norm_mul, abs_of_pos hr] using norm_sub_le (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) 1
  have hg : ‖outgoingRadialFirst k ‖x‖‖ ≤ (|k| * ‖x‖ + 1) / (4 * Real.pi * ‖x‖ ^ 2) := by
    simp only [outgoingRadialFirst, norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr.le, he, one_mul]
    norm_num [abs_of_pos Real.pi_pos]
    gcongr
  rw [kernelMagnetic, norm_smul]
  calc
    _ ≤ ‖-Complex.I * (k : ℂ) * outgoingRadialFirst k ‖x‖ / (‖x‖ : ℂ)‖ *
      (‖x‖ * ‖v‖) := by gcongr; simpa [complexify_norm] using cross_norm_le (complexify x) v
    _ = (|k| * ‖outgoingRadialFirst k ‖x‖‖ / ‖x‖) * (‖x‖ * ‖v‖) := by
      simp
    _ ≤ (|k| * ((|k| * ‖x‖ + 1) / (4 * Real.pi * ‖x‖ ^ 2)) / ‖x‖) *
      (‖x‖ * ‖v‖) := by gcongr
    _ = _ := by field_simp

/-- Exact single-source Silver--Müller defect, with the full physical dyadic
kernel. Its nonzero lower-order terms must be bounded uniformly before
integrating currents; no far-field identity is assumed. -/
theorem kernel_radiation_defect (k : ℝ) (x : Position) (hx : x ≠ 0) (v : Vector) :
    cross (kernelMagnetic k x v) (complexify (‖x‖⁻¹ • x)) - classicalDyadic k x v =
      (outgoingRadial k ‖x‖ / (‖x‖ : ℂ) ^ 2) • v +
      ((2 * Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 3) * outgoingRadial k ‖x‖ /
        (‖x‖ : ℂ) ^ 4) •
        (bilinear (complexify x) v • complexify x) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hc : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hn : ((x 0 : ℂ) ^ 2 + (x 1 : ℂ) ^ 2 + (x 2 : ℂ) ^ 2) = (‖x‖ : ℂ) ^ 2 := by
    have h := bilinear_complexify_self x
    simpa [bilinear, complexify, Fin.sum_univ_three, Complex.ofReal_pow, pow_two, add_assoc] using h
  ext i
  fin_cases i <;>
    simp [kernelMagnetic, classicalDyadic, cross, complexify, bilinear,
      outgoingRadial, outgoingRadialFirst, outgoingRadialSecond,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply, RCLike.inner_apply,
      PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, Fin.sum_univ_three,
      Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul]
  all_goals
    field_simp
    ring_nf
    simp only [Complex.I_sq]
  linear_combination (Complex.I * (k : ℂ) * (‖x‖ : ℂ) + (k : ℂ) ^ 2 * (‖x‖ : ℂ) ^ 2) * v 0 * hn
  linear_combination (Complex.I * (k : ℂ) * (‖x‖ : ℂ) + (k : ℂ) ^ 2 * (‖x‖ : ℂ) ^ 2) * v 1 * hn
  linear_combination (Complex.I * (k : ℂ) * (‖x‖ : ℂ) + (k : ℂ) ^ 2 * (‖x‖ : ℂ) ^ 2) * v 2 * hn

theorem kernel_radiation_defect_norm_le (k : ℝ) (x : Position) (hx : x ≠ 0) (v : Vector) :
    ‖cross (kernelMagnetic k x v) (complexify (‖x‖⁻¹ • x)) - classicalDyadic k x v‖ ≤
      (2 * |k| / (4 * Real.pi * ‖x‖ ^ 2) + 1 / (Real.pi * ‖x‖ ^ 3)) * ‖v‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc : 0 < 4 * Real.pi := by positivity
  have hg : ‖outgoingRadial k ‖x‖‖ = 1 / (4 * Real.pi * ‖x‖) := by
    rw [← outgoingGreen_eq_radial, outgoingGreen_norm, one_div]
  have ha : ‖outgoingRadial k ‖x‖ / (‖x‖ : ℂ) ^ 2‖ =
      (1 / (4 * Real.pi * ‖x‖)) / ‖x‖ ^ 2 := by
    simp [norm_pow, hg]
  have hb0 : ‖2 * Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 3‖ ≤ 2 * |k| * ‖x‖ + 3 := by
    have h := norm_sub_le (2 * Complex.I * (k : ℂ) * (‖x‖ : ℂ)) 3
    simpa [norm_mul, abs_of_pos hr] using h
  have hb : ‖(2 * Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 3) * outgoingRadial k ‖x‖ /
      (‖x‖ : ℂ) ^ 4‖ ≤ (2 * |k| * ‖x‖ + 3) *
        (1 / (4 * Real.pi * ‖x‖)) / ‖x‖ ^ 4 := by
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, hg]
    gcongr
  rw [kernel_radiation_defect k x hx v]
  calc
    _ ≤ ‖(outgoingRadial k ‖x‖ / (‖x‖ : ℂ) ^ 2) • v‖ +
      ‖((2 * Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 3) * outgoingRadial k ‖x‖ /
        (‖x‖ : ℂ) ^ 4) • (bilinear (complexify x) v • complexify x)‖ := norm_add_le _ _
    _ = ‖outgoingRadial k ‖x‖ / (‖x‖ : ℂ) ^ 2‖ * ‖v‖ +
      ‖(2 * Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 3) * outgoingRadial k ‖x‖ /
        (‖x‖ : ℂ) ^ 4‖ * ‖bilinear (complexify x) v • complexify x‖ := by simp only [norm_smul]
    _ ≤ ((1 / (4 * Real.pi * ‖x‖)) / ‖x‖ ^ 2) * ‖v‖ +
      ((2 * |k| * ‖x‖ + 3) * (1 / (4 * Real.pi * ‖x‖)) / ‖x‖ ^ 4) *
        (‖x‖ ^ 2 * ‖v‖) := by
      rw [ha]
      gcongr
      exact bilinear_radial_smul_norm_le x v
    _ = (2 * |k| / (4 * Real.pi * ‖x‖ ^ 2) + 1 / (Real.pi * ‖x‖ ^ 3)) * ‖v‖ := by
      field_simp
      ring

def radiationKernelConstant (k R : ℝ) : ℝ :=
  (2 * |k| + 4 + 2 * R * |k| * (|k| + 1)) / Real.pi

/-- Uniform estimate for every source point in the ball and every observation
direction. The observation direction is x/|x|, not (x-y)/|x-y|. -/
theorem displaced_kernel_radiation_norm_le (k R : ℝ) (hR : 0 ≤ R)
    (x y : Position) (hx : 2 * R + 2 ≤ ‖x‖) (hy : ‖y‖ ≤ R) (v : Vector) :
    ‖cross (kernelMagnetic k (x - y) v) (complexify (radialDirection x)) -
        classicalDyadic k (x - y) v‖ ≤ radiationKernelConstant k R / ‖x‖ ^ 2 * ‖v‖ := by
  have hr : 0 < ‖x‖ := by linarith
  have hs : 1 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
  have hsn : x - y ≠ 0 := norm_pos_iff.mp (by linarith)
  have hhalf : ‖x‖ / 2 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
  have hxy : ‖y‖ < ‖x‖ := by linarith
  have hd : ‖complexify (radialDirection x) - complexify (radialDirection (x - y))‖ ≤
      2 * R / ‖x - y‖ := by
    rw [← complexify_sub, complexify_norm, norm_sub_rev]
    exact (radialDirection_sub_norm_le_distance x y hxy).trans (by gcongr)
  have hm : ‖kernelMagnetic k (x - y) v‖ ≤
      (|k| * (|k| + 1) / (4 * Real.pi * ‖x - y‖)) * ‖v‖ := by
    apply (kernelMagnetic_norm_le k (x - y) hsn v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    calc
      _ ≤ |k| * ((|k| + 1) * ‖x - y‖) / (4 * Real.pi * ‖x - y‖ ^ 2) := by
        gcongr
        nlinarith [abs_nonneg k]
      _ = _ := by field_simp
  have hf : ‖cross (kernelMagnetic k (x - y) v) (complexify (radialDirection (x - y))) -
      classicalDyadic k (x - y) v‖ ≤ ((2 * |k| + 4) / (4 * Real.pi * ‖x - y‖ ^ 2)) * ‖v‖ := by
    apply (kernel_radiation_defect_norm_le k (x - y) hsn v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    have hb : 1 / (Real.pi * ‖x - y‖ ^ 3) ≤ 1 / (Real.pi * ‖x - y‖ ^ 2) := by
      gcongr
      nlinarith [sq_nonneg ‖x - y‖]
    calc
      _ ≤ 2 * |k| / (4 * Real.pi * ‖x - y‖ ^ 2) + 1 / (Real.pi * ‖x - y‖ ^ 2) := add_le_add le_rfl hb
      _ = _ := by field_simp
  have he : cross (kernelMagnetic k (x - y) v) (complexify (radialDirection x)) -
      classicalDyadic k (x - y) v =
    (cross (kernelMagnetic k (x - y) v) (complexify (radialDirection (x - y))) -
      classicalDyadic k (x - y) v) +
      cross (kernelMagnetic k (x - y) v)
        (complexify (radialDirection x) - complexify (radialDirection (x - y))) := by
    rw [cross_sub_right]
    abel
  rw [he]
  calc
    _ ≤ ‖cross (kernelMagnetic k (x - y) v) (complexify (radialDirection (x - y))) -
      classicalDyadic k (x - y) v‖ +
      ‖cross (kernelMagnetic k (x - y) v)
        (complexify (radialDirection x) - complexify (radialDirection (x - y)))‖ := norm_add_le _ _
    _ ≤ ((2 * |k| + 4) / (4 * Real.pi * ‖x - y‖ ^ 2)) * ‖v‖ +
      ((|k| * (|k| + 1) / (4 * Real.pi * ‖x - y‖)) * ‖v‖) * (2 * R / ‖x - y‖) := by
      gcongr
      apply (cross_norm_le _ _).trans
      gcongr
    _ = ((2 * |k| + 4 + 2 * R * |k| * (|k| + 1)) /
      (4 * Real.pi * ‖x - y‖ ^ 2)) * ‖v‖ := by field_simp
    _ ≤ ((2 * |k| + 4 + 2 * R * |k| * (|k| + 1)) /
      (4 * Real.pi * (‖x‖ / 2) ^ 2)) * ‖v‖ := by gcongr
    _ = radiationKernelConstant k R / ‖x‖ ^ 2 * ‖v‖ := by
      unfold radiationKernelConstant
      field_simp
      ring

end OQ7Prescribed
