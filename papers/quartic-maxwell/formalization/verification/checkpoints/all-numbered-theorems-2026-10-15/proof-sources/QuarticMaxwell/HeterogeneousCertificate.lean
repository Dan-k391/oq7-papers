import QuarticMaxwell.TwoSphereGeometry
import QuarticMaxwell.BlockSourceMoments
import QuarticMaxwell.FixedPatternScattering
import QuarticMaxwell.FixedPatternContrast

/-! Actual continuum moments for the dated heterogeneous two-sphere example.
The geometry, material inverse, isolated means and all interactions are actual. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace QuarticMaxwell.HeterogeneousCertificate
open MeasureTheory Set OQ7Prescribed TwoSphereGeometry TwoSupportStatic TwoSupportBounds
open FixedPatternWork FixedPatternScattering

def body (n : UnitSphere) : WeakMaterial.Medium :=
  medium n (1 / 20) (by norm_num) (by norm_num) heterogeneous

def volume (n : UnitSphere) : ℝ := MeasureTheory.volume.real (body n).domain

def isolated (n : UnitSphere) : DomainL2 (body n).domain →L[ℂ] DomainL2 (body n).domain :=
  blockInverse (leftBall n (1 / 20)) (rightBall n (1 / 20)) measurableSet_ball measurableSet_ball heterogeneous

def isolatedMoment0 (n : UnitSphere) (e : Vector) : Vector :=
  MomentOperator.map (body n).domain (body n).finite (isolated n (constantInput (body n) e))

def isolatedMoment1 (n : UnitSphere) (e : Vector) : Vector :=
  MomentOperator.map (body n).domain (body n).finite (isolated n (linearInput (body n) n e))

theorem volume_eq (n : UnitSphere) : volume n = 3 * Real.pi / 2000 := by
  unfold volume body
  rw [medium_volume]
  ring

theorem volume_pos (n : UnitSphere) : 0 < volume n := by rw [volume_eq]; positivity

theorem static_difference (n : UnitSphere) : ‖staticResponse (body n) - isolated n‖ < 1 / 600 :=
  fixed_static_difference n

theorem isolated_norm (n : UnitSphere) : ‖isolated n‖ ≤ 2 := by
  have h := blockInverse_norm_le (leftBall n (1 / 20)) (rightBall n (1 / 20))
    Metric.isOpen_ball Metric.isOpen_ball (gap (1 / 20)) (gap_pos (by norm_num))
    (sphere_separation n (1 / 20)) heterogeneous
  simpa only [isolated, heterogeneous_rho] using h

theorem constant_norm_sq (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖constantInput (body n) e‖ ^ 2 = volume n := by
  have h := SourceTaylor.constant_norm_sq (body n).domain (body n).measurable (body n).finite n e
  simpa only [constantInput, volume, he, one_pow, mul_one] using h

theorem constant_norm (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖constantInput (body n) e‖ = Real.sqrt (volume n) := by
  rw [← constant_norm_sq n e he, Real.sqrt_sq (norm_nonneg _)]

theorem linear_norm (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖linearInput (body n) n e‖ ≤ (3 / 5) * Real.sqrt (volume n) := by
  have h := SourceTaylor.moment_norm (body n).domain (body n).measurable (body n).finite n e (body n).subset_ball
  change ‖linearInput (body n) n e‖ ≤ (3 / 5) * ‖constantInput (body n) e‖ at h
  rw [constant_norm n e he] at h
  exact h

theorem moment_norm (n : UnitSphere) (p : DomainL2 (body n).domain) :
    ‖MomentOperator.map (body n).domain (body n).finite p‖ ≤ Real.sqrt (volume n) * ‖p‖ :=
  MomentOperator.norm_le (body n).domain (body n).finite p

theorem isolatedMoment0_norm (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖isolatedMoment0 n e‖ ≤ 2 * volume n := by
  have hA := ((isolated n).le_opNorm (constantInput (body n) e)).trans
    (mul_le_mul_of_nonneg_right (isolated_norm n) (norm_nonneg _))
  rw [constant_norm n e he] at hA
  apply (moment_norm n _).trans
  calc
    _ ≤ Real.sqrt (volume n) * (2 * Real.sqrt (volume n)) :=
      mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
    _ = _ := by nlinarith only [Real.sq_sqrt (volume_pos n).le]

theorem isolatedMoment1_norm (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖isolatedMoment1 n e‖ ≤ (6 / 5) * volume n := by
  have hA := ((isolated n).le_opNorm (linearInput (body n) n e)).trans
    (mul_le_mul (isolated_norm n) (linear_norm n e he) (norm_nonneg _) (by norm_num))
  apply (moment_norm n _).trans
  calc
    _ ≤ Real.sqrt (volume n) * (2 * ((3 / 5) * Real.sqrt (volume n))) :=
      mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
    _ = _ := by nlinarith only [Real.sq_sqrt (volume_pos n).le]

theorem moment0_error (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖moment0 (body n) e - isolatedMoment0 n e‖ ≤ volume n / 600 := by
  have h := MomentOperator.response_difference_norm_le (body n).domain (body n).finite
    (staticResponse (body n)) (isolated n) (static_difference n).le (constantInput (body n) e)
  change ‖moment0 (body n) e - isolatedMoment0 n e‖ ≤
    Real.sqrt (volume n) * (1 / 600) * ‖constantInput (body n) e‖ at h
  rw [constant_norm n e he] at h
  apply h.trans
  apply le_of_eq
  nlinarith only [Real.sq_sqrt (volume_pos n).le]

theorem moment1_error (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    ‖moment1 (body n) n e - isolatedMoment1 n e‖ ≤ (3 / 5) * volume n / 600 := by
  have h := MomentOperator.response_difference_norm_le (body n).domain (body n).finite
    (staticResponse (body n)) (isolated n) (static_difference n).le (linearInput (body n) n e)
  change ‖moment1 (body n) n e - isolatedMoment1 n e‖ ≤
    Real.sqrt (volume n) * (1 / 600) * ‖linearInput (body n) n e‖ at h
  apply h.trans
  calc
    _ ≤ Real.sqrt (volume n) * (1 / 600) * ((3 / 5) * Real.sqrt (volume n)) :=
      mul_le_mul_of_nonneg_left (linear_norm n e he) (by positivity)
    _ = _ := by nlinarith only [Real.sq_sqrt (volume_pos n).le]

def b0 : ℂ := ⟨111 / 130, 173 / 130⟩
def b1 : ℂ := ⟨307 / 780, 147 / 260⟩

theorem beta_left : SphereResponse.beta Complex.I = ⟨3 / 10, 9 / 10⟩ := by
  apply Complex.ext <;> norm_num [SphereResponse.beta, Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem beta_right : SphereResponse.beta (2 * Complex.I) = ⟨12 / 13, 18 / 13⟩ := by
  apply Complex.ext <;> norm_num [SphereResponse.beta, Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem isolatedMoment0_formula (n : UnitSphere) (e : Vector) :
    isolatedMoment0 n e = ((volume n : ℂ) * b0) • e := by
  have h := BlockSourceMoments.moment_blockInverse_constant (leftCenter n) (rightCenter n)
    (1 / 20) (2 * (1 / 20)) (by norm_num) (by norm_num) heterogeneous e
  change isolatedMoment0 n e =
    (SphereResponse.beta Complex.I * ((MeasureTheory.volume.real (leftBall n (1 / 20)) : ℝ) : ℂ) +
      SphereResponse.beta (2 * Complex.I) * ((MeasureTheory.volume.real (rightBall n (1 / 20)) : ℝ) : ℂ)) • e at h
  rw [beta_left, beta_right, left_volume n (by norm_num), right_volume n (by norm_num)] at h
  rw [h]
  congr 1
  rw [volume_eq]
  apply Complex.ext <;> simp [b0, Complex.mul_re, Complex.mul_im] <;> ring_nf <;> norm_num <;> ring

theorem direction_leftCenter (n : UnitSphere) : inner ℝ (n : Position) (leftCenter n) = -1 / 2 := by
  simp [leftCenter, inner_smul_right, inner_self_eq_norm_sq_to_K]

theorem direction_rightCenter (n : UnitSphere) : inner ℝ (n : Position) (rightCenter n) = 1 / 2 := by
  simp [rightCenter, inner_smul_right, inner_self_eq_norm_sq_to_K]

theorem isolatedMoment1_formula (n : UnitSphere) (e : Vector) :
    isolatedMoment1 n e = ((volume n : ℂ) * b1) • e := by
  have hsub : BlockSourceMoments.joined (leftCenter n) (rightCenter n) (1 / 20) (2 * (1 / 20)) ⊆
      Metric.closedBall (0 : Position) (3 / 5) := domain_subset n (by norm_num)
  have h := BlockSourceMoments.moment_blockInverse_affine (leftCenter n) (rightCenter n)
    (1 / 20) (2 * (1 / 20)) (by norm_num) (by norm_num) heterogeneous n e (3 / 5) hsub
  change isolatedMoment1 n e =
    (SphereResponse.beta Complex.I * (((inner ℝ (n : Position) (leftCenter n) * MeasureTheory.volume.real (leftBall n (1 / 20)) : ℝ) : ℂ)) +
      SphereResponse.beta (2 * Complex.I) * (((inner ℝ (n : Position) (rightCenter n) * MeasureTheory.volume.real (rightBall n (1 / 20)) : ℝ) : ℂ))) • e at h
  rw [direction_leftCenter, direction_rightCenter, beta_left, beta_right,
    left_volume n (by norm_num), right_volume n (by norm_num)] at h
  rw [h]
  congr 1
  rw [volume_eq]
  apply Complex.ext <;> simp [b1, Complex.mul_re, Complex.mul_im] <;> ring_nf <;> norm_num <;> ring

def I0 (n : UnitSphere) (e : Vector) : ℝ := (inner ℂ (moment0 (body n) e) (moment1 (body n) n e)).im

theorem isolated_imaginary_moment (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    (inner ℂ (isolatedMoment0 n e) (isolatedMoment1 n e)).im = -(8 / 195) * volume n ^ 2 := by
  have he' : inner ℂ e e = 1 := by simp [inner_self_eq_norm_sq_to_K, he]
  rw [isolatedMoment0_formula, isolatedMoment1_formula, inner_smul_left, inner_smul_right, he']
  simp [b0, b1, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem isolated_extinction (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    (inner ℂ e (isolatedMoment0 n e)).im = (173 / 130) * volume n := by
  have he' : inner ℂ e e = 1 := by simp [inner_self_eq_norm_sq_to_K, he]
  rw [isolatedMoment0_formula, inner_smul_right, he']
  simp [b0, Complex.mul_im]
  ring

theorem imaginary_moment_error (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    |I0 n e + (8 / 195) * volume n ^ 2| ≤
      (3 / 5) * (4 * (1 / 600) + (1 / 600) ^ 2) * volume n ^ 2 := by
  have h := FixedPatternWork.inner_im_error (moment0 (body n) e) (moment1 (body n) n e)
    (isolatedMoment0 n e) (isolatedMoment1 n e)
  rw [isolated_imaginary_moment n e he] at h
  change |I0 n e - (-(8 / 195) * volume n ^ 2)| ≤ _ at h
  have hn1 : ‖moment1 (body n) n e‖ ≤ (3 / 5) * volume n / 600 + (6 / 5) * volume n := by
    calc
      _ = ‖(moment1 (body n) n e - isolatedMoment1 n e) + isolatedMoment1 n e‖ := by rw [sub_add_cancel]
      _ ≤ ‖moment1 (body n) n e - isolatedMoment1 n e‖ + ‖isolatedMoment1 n e‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (moment1_error n e he) (isolatedMoment1_norm n e he)
  have hV := (volume_pos n).le
  have h' : |I0 n e - (-(8 / 195) * volume n ^ 2)| ≤
      (3 / 5) * (4 * (1 / 600) + (1 / 600) ^ 2) * volume n ^ 2 := by
    apply h.trans
    calc
      _ ≤ (volume n / 600) * ((3 / 5) * volume n / 600 + (6 / 5) * volume n) +
          (2 * volume n) * ((3 / 5) * volume n / 600) := by
        exact add_le_add (mul_le_mul (moment0_error n e he) hn1 (norm_nonneg _) (by positivity))
          (mul_le_mul (isolatedMoment0_norm n e he) (moment1_error n e he) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  simpa only [neg_mul, sub_neg_eq_add] using h'

theorem extinction_error (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    |D0 (body n) e - (173 / 130) * volume n| ≤ volume n / 600 := by
  rw [← isolated_extinction n e he, denominator_moment]
  calc
    _ = |(inner ℂ e (moment0 (body n) e - isolatedMoment0 n e)).im| := by
      rw [inner_sub_right, Complex.sub_im]
    _ ≤ ‖inner ℂ e (moment0 (body n) e - isolatedMoment0 n e)‖ := Complex.abs_im_le_norm _
    _ ≤ ‖e‖ * ‖moment0 (body n) e - isolatedMoment0 n e‖ := norm_inner_le_norm _ _
    _ ≤ _ := by rw [he, one_mul]; exact moment0_error n e he

theorem extinction_interval (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    (10367 / 7800) * volume n ≤ D0 (body n) e ∧ D0 (body n) e ≤ (10393 / 7800) * volume n := by
  have h := abs_le.mp (extinction_error n e he)
  constructor <;> linarith

theorem imaginary_moment_interval (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    (12 / 325) * volume n ^ 2 ≤ |I0 n e| ∧ |I0 n e| ≤ (44 / 975) * volume n ^ 2 := by
  have h := imaginary_moment_error n e he
  have hr : (3 / 5 : ℝ) * (4 * (1 / 600) + (1 / 600) ^ 2) ≤ (1 / 10) * (8 / 195) := by norm_num
  have h' := h.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg (volume n)))
  have hbounds := abs_le.mp h'
  have hneg : I0 n e ≤ 0 := by nlinarith only [hbounds.2, sq_nonneg (volume n)]
  rw [abs_of_nonpos hneg]
  constructor <;> nlinarith only [hbounds.1, hbounds.2]

theorem imaginary_moment_negative (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) : I0 n e < 0 := by
  have h := (abs_le.mp (imaginary_moment_error n e he)).2
  have hv := sq_pos_of_pos (volume_pos n)
  nlinarith only [h, hv]

theorem coefficient_formula (n : UnitSphere) (e : Vector) :
    FixedPatternContrast.coefficient (body n) n e = (2 / (3 * Real.pi)) * |I0 n e| / D0 (body n) e := by
  change |(2 / (3 * Real.pi)) * I0 n e| / D0 (body n) e = _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (3 * Real.pi))]

/-- The exact original interval is for the genuine interacting continuum
coefficient, not the isolated comparison and not a point-dipole model. -/
theorem coefficient_interval (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1) :
    36 / 1299125 ≤ FixedPatternContrast.coefficient (body n) n e ∧
      FixedPatternContrast.coefficient (body n) n e ≤ 44 / 1295875 := by
  have hI := imaginary_moment_interval n e he
  have hD := extinction_interval n e he
  have hpos : 0 < D0 (body n) e := lt_of_lt_of_le
    (show 0 < (10367 / 7800) * volume n by have hw := volume_pos n; positivity) hD.1
  rw [coefficient_formula]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    calc
      _ ≤ (36 / 1299125) * ((10393 / 7800) * volume n) :=
        mul_le_mul_of_nonneg_left hD.2 (by norm_num)
      _ = (2 / (3 * Real.pi)) * ((12 / 325) * volume n ^ 2) := by
        rw [volume_eq]
        field_simp [Real.pi_ne_zero]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hI.1 (by positivity)
  · apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ (2 / (3 * Real.pi)) * ((44 / 975) * volume n ^ 2) :=
        mul_le_mul_of_nonneg_left hI.2 (by positivity)
      _ = (44 / 1295875) * ((10367 / 7800) * volume n) := by
        rw [volume_eq]
        field_simp [Real.pi_ne_zero]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD.1 (by norm_num)

end QuarticMaxwell.HeterogeneousCertificate
