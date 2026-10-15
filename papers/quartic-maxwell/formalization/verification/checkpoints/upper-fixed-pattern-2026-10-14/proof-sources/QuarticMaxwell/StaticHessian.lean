import QuarticMaxwell.ProjectionKernel
import PrescribedExtinction.NewtonPV
import PrescribedExtinction.RadiationKernel

/-! Sharp operator and separated-point difference estimates for the actual
classical Newton Hessian. Distribution/current association is separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace QuarticMaxwell.StaticHessian
open OQ7Prescribed

def newtonHessianOperator (r : Position) : Vector →L[ℂ] Vector :=
  (((1 / (4 * Real.pi * ‖r‖ ^ 3) : ℝ) : ℂ)) •
    ((3 : ℂ) • radialProjection r - ContinuousLinearMap.id ℂ Vector)

theorem newtonHessianOperator_measurable : Measurable newtonHessianOperator := by
  have hr := rankOne_complexify_continuous.measurable
  unfold newtonHessianOperator radialProjection
  fun_prop

theorem newtonHessianOperator_apply (r : Position) (v : Vector) (i : Fin 3) :
    (newtonHessianOperator r v) i = ∑ j, (newtonHessianKernel i j r : ℂ) * v j := by
  by_cases hr : r = 0
  · subst r
    simp [newtonHessianOperator, newtonHessianKernel]
  have hn : (‖r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  fin_cases i <;>
    simp [newtonHessianOperator, newtonHessianKernel, radialProjection,
      InnerProductSpace.rankOne_apply, complexify, PiLp.inner_apply, RCLike.inner_apply,
      PiLp.smul_apply, PiLp.sub_apply, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv, Fin.sum_univ_succ]
  all_goals field_simp; ring

theorem projectionTriple_norm_le (r : Position) (hr : r ≠ 0) :
    ‖(3 : ℂ) • radialProjection r - ContinuousLinearMap.id ℂ Vector‖ ≤ 2 := by
  have he : (3 : ℂ) • radialProjection r - ContinuousLinearMap.id ℂ Vector =
      (2 : ℂ) • radialProjection r + (-1 : ℂ) •
        (ContinuousLinearMap.id ℂ Vector - radialProjection r) := by module
  rw [he]
  apply orthogonal_split_norm_le (radialProjection r) (radialProjection_orthogonal r hr)
  all_goals norm_num

theorem newtonHessianOperator_norm_le (r : Position) (hr : r ≠ 0) :
    ‖newtonHessianOperator r‖ ≤ 1 / (2 * Real.pi * ‖r‖ ^ 3) := by
  unfold newtonHessianOperator
  calc
    _ ≤ ‖(((1 / (4 * Real.pi * ‖r‖ ^ 3) : ℝ) : ℂ))‖ *
        ‖(3 : ℂ) • radialProjection r - ContinuousLinearMap.id ℂ Vector‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (1 / (4 * Real.pi * ‖r‖ ^ 3)) * 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (projectionTriple_norm_le r hr) (by positivity)
    _ = _ := by ring

def normalizedComplex (r : Position) : Vector := ((‖r‖⁻¹ : ℝ) : ℂ) • complexify r

theorem normalizedComplex_norm (r : Position) (hr : r ≠ 0) : ‖normalizedComplex r‖ = 1 := by
  simp [normalizedComplex, norm_smul, complexify_norm, norm_ne_zero_iff.mpr hr]

theorem normalizedComplex_projection (r : Position) :
    InnerProductSpace.rankOne ℂ (normalizedComplex r) (normalizedComplex r) = radialProjection r := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [normalizedComplex, radialProjection, InnerProductSpace.rankOne_apply,
    inner_smul_left, smul_apply, smul_smul, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

theorem normalizedComplex_difference (r s : Position) {d : ℝ} (hd : 0 < d)
    (hr : d ≤ ‖r‖) (hs : d ≤ ‖s‖) :
    ‖normalizedComplex r - normalizedComplex s‖ ≤ 2 / d * ‖r - s‖ := by
  have hr0 : 0 < ‖r‖ := lt_of_lt_of_le hd hr
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hd hs
  have he : normalizedComplex r - normalizedComplex s =
      ((‖r‖⁻¹ : ℝ) : ℂ) • complexify (r - s) +
      (((‖r‖⁻¹ - ‖s‖⁻¹ : ℝ) : ℂ)) • complexify s := by
    rw [complexify_sub]
    unfold normalizedComplex
    push_cast
    module
  have hscalar : |‖r‖⁻¹ - ‖s‖⁻¹| * ‖s‖ = |‖s‖ - ‖r‖| / ‖r‖ := by
    have heq : ‖r‖⁻¹ - ‖s‖⁻¹ = (‖s‖ - ‖r‖) / (‖r‖ * ‖s‖) := by field_simp
    rw [heq, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hs0]
    field_simp
  rw [he]
  calc
    _ ≤ ‖((‖r‖⁻¹ : ℝ) : ℂ) • complexify (r - s)‖ +
        ‖(((‖r‖⁻¹ - ‖s‖⁻¹ : ℝ) : ℂ)) • complexify s‖ := norm_add_le _ _
    _ = ‖r‖⁻¹ * ‖r - s‖ + |‖s‖ - ‖r‖| / ‖r‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, complexify_norm,
        abs_inv, abs_of_pos hr0]
      rw [hscalar]
    _ ≤ ‖r‖⁻¹ * ‖r - s‖ + ‖r - s‖ / ‖r‖ := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hr0.le
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le s r
    _ = 2 / ‖r‖ * ‖r - s‖ := by ring
    _ ≤ _ := by gcongr

theorem radialProjection_difference (r s : Position) {d : ℝ} (hd : 0 < d)
    (hr : d ≤ ‖r‖) (hs : d ≤ ‖s‖) :
    ‖radialProjection r - radialProjection s‖ ≤ 4 / d * ‖r - s‖ := by
  let u := normalizedComplex r
  let v := normalizedComplex s
  have hu : ‖u‖ = 1 := normalizedComplex_norm r (norm_pos_iff.mp (lt_of_lt_of_le hd hr))
  have hv : ‖v‖ = 1 := normalizedComplex_norm s (norm_pos_iff.mp (lt_of_lt_of_le hd hs))
  have he : radialProjection r - radialProjection s =
      InnerProductSpace.rankOne ℂ (u - v) u + InnerProductSpace.rankOne ℂ v (u - v) := by
    rw [← normalizedComplex_projection r, ← normalizedComplex_projection s]
    apply ContinuousLinearMap.ext
    intro z
    change inner ℂ u z • u - inner ℂ v z • v =
      inner ℂ u z • (u - v) + inner ℂ (u - v) z • v
    simp only [inner_sub_left, sub_smul, smul_sub]
    module
  rw [he]
  calc
    _ ≤ ‖InnerProductSpace.rankOne ℂ (u - v) u‖ +
        ‖InnerProductSpace.rankOne ℂ v (u - v)‖ := norm_add_le _ _
    _ = 2 * ‖u - v‖ := by rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne, hu, hv]; ring
    _ ≤ 2 * (2 / d * ‖r - s‖) := mul_le_mul_of_nonneg_left (normalizedComplex_difference r s hd hr hs) (by norm_num)
    _ = _ := by ring

theorem reciprocal_cube_difference {a b d : ℝ} (hd : 0 < d) (ha : d ≤ a) (hb : d ≤ b) :
    |1 / a ^ 3 - 1 / b ^ 3| ≤ 3 / d ^ 4 * |a - b| := by
  have ha0 : 0 < a := lt_of_lt_of_le hd ha
  have hb0 : 0 < b := lt_of_lt_of_le hd hb
  have hsum : 0 ≤ 1 / (a * b ^ 3) + 1 / (a ^ 2 * b ^ 2) + 1 / (a ^ 3 * b) := by positivity
  have h₁ : d ^ 4 ≤ a * b ^ 3 := by
    calc
      _ = d * d ^ 3 := by ring
      _ ≤ _ := by gcongr
  have h₂ : d ^ 4 ≤ a ^ 2 * b ^ 2 := by
    calc
      _ = d ^ 2 * d ^ 2 := by ring
      _ ≤ _ := by gcongr
  have h₃ : d ^ 4 ≤ a ^ 3 * b := by
    calc
      _ = d ^ 3 * d := by ring
      _ ≤ _ := by gcongr
  have hfrac : 1 / (a * b ^ 3) + 1 / (a ^ 2 * b ^ 2) + 1 / (a ^ 3 * b) ≤ 3 / d ^ 4 := by
    have h1 := one_div_le_one_div_of_le (pow_pos hd 4) h₁
    have h2 := one_div_le_one_div_of_le (pow_pos hd 4) h₂
    have h3 := one_div_le_one_div_of_le (pow_pos hd 4) h₃
    calc
      _ ≤ 1 / d ^ 4 + 1 / d ^ 4 + 1 / d ^ 4 := add_le_add (add_le_add h1 h2) h3
      _ = _ := by ring
  have he : 1 / a ^ 3 - 1 / b ^ 3 =
      (b - a) * (1 / (a * b ^ 3) + 1 / (a ^ 2 * b ^ 2) + 1 / (a ^ 3 * b)) := by field_simp; ring
  rw [he, abs_mul, abs_of_nonneg hsum, abs_sub_comm]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfrac (abs_nonneg (a - b))

theorem hessian_scalar_difference (r s : Position) {d : ℝ} (hd : 0 < d)
    (hr : d ≤ ‖r‖) (hs : d ≤ ‖s‖) :
    ‖(((1 / (4 * Real.pi * ‖r‖ ^ 3) : ℝ) : ℂ)) -
      (((1 / (4 * Real.pi * ‖s‖ ^ 3) : ℝ) : ℂ))‖ ≤
      3 / (4 * Real.pi * d ^ 4) * ‖r - s‖ := by
  have he : 1 / (4 * Real.pi * ‖r‖ ^ 3) - 1 / (4 * Real.pi * ‖s‖ ^ 3) =
      1 / (4 * Real.pi) * (1 / ‖r‖ ^ 3 - 1 / ‖s‖ ^ 3) := by ring
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, he, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (4 * Real.pi))]
  calc
    _ ≤ (1 / (4 * Real.pi)) * (3 / d ^ 4 * |‖r‖ - ‖s‖|) :=
      mul_le_mul_of_nonneg_left (reciprocal_cube_difference hd hr hs) (by positivity)
    _ ≤ (1 / (4 * Real.pi)) * (3 / d ^ 4 * ‖r - s‖) := by
      gcongr
      exact abs_norm_sub_norm_le r s
    _ = _ := by ring

/-- This bound needs only separated nonzero endpoints and is consequently
stronger in scope than a line-segment minimum-distance hypothesis. -/
theorem newtonHessianOperator_difference (r s : Position) {d : ℝ} (hd : 0 < d)
    (hr : d ≤ ‖r‖) (hs : d ≤ ‖s‖) :
    ‖newtonHessianOperator r - newtonHessianOperator s‖ ≤
      6 / (Real.pi * d ^ 4) * ‖r - s‖ := by
  let a : ℂ := (((1 / (4 * Real.pi * ‖r‖ ^ 3) : ℝ) : ℂ))
  let b : ℂ := (((1 / (4 * Real.pi * ‖s‖ ^ 3) : ℝ) : ℂ))
  let P := (3 : ℂ) • radialProjection r - ContinuousLinearMap.id ℂ Vector
  let Q := (3 : ℂ) • radialProjection s - ContinuousLinearMap.id ℂ Vector
  have he : newtonHessianOperator r - newtonHessianOperator s =
      a • (P - Q) + (a - b) • Q := by unfold newtonHessianOperator; dsimp [a, b, P, Q]; module
  have ha : ‖a‖ ≤ 1 / (4 * Real.pi * d ^ 3) := by
    dsimp [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  have hb := hessian_scalar_difference r s hd hr hs
  have hQ : ‖Q‖ ≤ 2 := projectionTriple_norm_le s (norm_pos_iff.mp (lt_of_lt_of_le hd hs))
  have hPQ : ‖P - Q‖ ≤ 12 / d * ‖r - s‖ := by
    have heq : P - Q = (3 : ℂ) • (radialProjection r - radialProjection s) := by dsimp [P, Q]; module
    rw [heq]
    calc
      _ ≤ ‖(3 : ℂ)‖ * ‖radialProjection r - radialProjection s‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 3 * (4 / d * ‖r - s‖) := by
        norm_num only [Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (radialProjection_difference r s hd hr hs) (by norm_num)
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ ‖a • (P - Q)‖ + ‖(a - b) • Q‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖P - Q‖ + ‖a - b‖ * ‖Q‖ :=
      add_le_add (ContinuousLinearMap.opNorm_smul_le _ _) (ContinuousLinearMap.opNorm_smul_le _ _)
    _ ≤ (1 / (4 * Real.pi * d ^ 3)) * (12 / d * ‖r - s‖) +
        (3 / (4 * Real.pi * d ^ 4) * ‖r - s‖) * 2 := by
      exact add_le_add (mul_le_mul ha hPQ (norm_nonneg _) (by positivity))
        (mul_le_mul hb hQ (norm_nonneg _) (by positivity))
    _ = (9 / (2 * Real.pi * d ^ 4)) * ‖r - s‖ := by field_simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.pi * d ^ 4)
        (by positivity : 0 < Real.pi * d ^ 4)).mpr
      nlinarith [mul_pos Real.pi_pos (pow_pos hd 4)]

end QuarticMaxwell.StaticHessian
