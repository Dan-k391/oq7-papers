import QuarticMaxwell.HomogeneousMoments

/-! Quantitative error estimates for actual homogeneous finite-sphere moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed SphereStatic SphereResponse SphereExterior SphereDoubleMean
  BlockSourceMoments BlockInteractionMoments TwoSupportStatic TwoSupportBounds TwoSphereGeometry
  SourceTaylor FixedPatternWork FixedPatternScattering MeasureTheory Set

def affineCoefficient : ℝ := 256 * Real.sqrt 3 * Real.pi / (3 * (4 / 5 : ℝ) ^ 4)

theorem affineCoefficient_pos : 0 < affineCoefficient := by unfold affineCoefficient; positivity

theorem Parameters.center_separation (P : Parameters) :
    P.a + 2 * P.a < ‖leftCenter P.n - rightCenter P.n‖ := by
  rw [center_distance]
  linarith [P.a_small]

theorem Parameters.reverse_separation (P : Parameters) :
    ∀ x ∈ rightBall P.n P.a, ∀ y ∈ leftBall P.n P.a, gap P.a ≤ ‖x - y‖ := by
  intro x hx y hy
  simpa only [norm_sub_rev] using sphere_separation P.n P.a y hy x hx

theorem Parameters.p1c_norm (P : Parameters) :
    ‖P.p1c‖ ≤ affineCoefficient * P.μ ^ 2 * P.a ^ 8 := by
  have h := first_affine_moment (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) (gap P.a) (gap_pos P.a_small) P.center_separation
    (sphere_separation P.n P.a) P.material P.n P.electric (3 / 5) (domain_subset P.n P.a_small)
  change P.p1c = _ at h
  rw [P.center_projection_left, P.center_projection_right] at h
  norm_num only [neg_div, neg_add_cancel, zero_mul, Complex.ofReal_zero, mul_zero, zero_smul, zero_add] at h
  dsimp only [Parameters.material, homogeneousPair] at h
  have hL := first_odd_cross_norm (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) (gap P.a) (gap_pos P.a_small) P.center_separation
    (sphere_separation P.n P.a) P.μ P.μ_pos (P.n : OQ7Prescribed.Position) (by simp)
    P.electric P.electric_norm
  have hR := first_odd_cross_norm (rightCenter P.n) (leftCenter P.n) (2 * P.a) P.a
    (by linarith [P.a_pos]) P.a_pos (gap P.a) (gap_pos P.a_small)
    (by rw [norm_sub_rev]; linarith [P.center_separation]) P.reverse_separation
    P.μ P.μ_pos (P.n : OQ7Prescribed.Position) (by simp) P.electric P.electric_norm
  rw [ball_inverse_moment _ _ P.a_pos] at hL
  rw [ball_inverse_moment _ _ (by linarith [P.a_pos] : 0 < 2 * P.a)] at hR
  have hsum := (norm_add_le _ _).trans (add_le_add hL hR)
  change ‖_ + _‖ ≤ _ at hsum
  rw [← h] at hsum
  rw [ball_volume_real (leftCenter P.n) P.a_pos.le,
    ball_volume_real (rightCenter P.n) (by linarith [P.a_pos] : 0 ≤ 2 * P.a)] at hsum
  have hgap : (4 / 5 : ℝ) ≤ gap P.a := by unfold gap; linarith [P.a_small]
  have hβ := HomogeneousScalars.beta_norm_le_mu P.μ_pos.le
  have hfactor : 6 * Real.sqrt 3 / (5 * Real.pi * (gap P.a) ^ 4) ≤
      6 * Real.sqrt 3 / (5 * Real.pi * (4 / 5 : ℝ) ^ 4) := by gcongr
  apply hsum.trans
  calc
    _ ≤ (6 * Real.sqrt 3 / (5 * Real.pi * (4 / 5 : ℝ) ^ 4)) * P.μ * P.μ * (2 * P.a) ^ 2 *
          (4 * Real.pi * P.a ^ 3 / 3) * (4 * Real.pi * (2 * P.a) ^ 3 / 3) +
        (6 * Real.sqrt 3 / (5 * Real.pi * (4 / 5 : ℝ) ^ 4)) * P.μ * P.μ * P.a ^ 2 *
          (4 * Real.pi * (2 * P.a) ^ 3 / 3) * (4 * Real.pi * P.a ^ 3 / 3) := by
      gcongr <;> first | exact hfactor | exact hβ | positivity [P.μ_pos, P.a_pos]
    _ = _ := by unfold affineCoefficient; field_simp [Real.pi_ne_zero]; ring

theorem Parameters.resolvent_error (P : Parameters) :
    ‖staticResponse P.body - P.A - P.A ∘L P.C ∘L P.A‖ ≤ 16 * P.μ ^ 3 * P.a ^ 6 := by
  have h := homogeneous_remainder (leftBall P.n P.a) (rightBall P.n P.a)
    Metric.isOpen_ball Metric.isOpen_ball (ball_measure_ne_top _ _) (ball_measure_ne_top _ _)
    (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (left_subset P.n P.a_small) (right_subset P.n P.a_small) (gap P.a) (gap_pos P.a_small)
    (sphere_separation P.n P.a) P.μ P.μ_pos
  rw [response_eq_staticResponse P.n P.a P.a_pos P.a_small (homogeneousPair P.μ P.μ_pos)] at h
  change ‖staticResponse P.body - P.A - P.A ∘L P.C ∘L P.A‖ ≤ _ at h
  apply h.trans
  calc
    _ ≤ P.μ ^ 3 * (4 * P.a ^ 3) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [P.μ_pos])
      exact (sq_le_sq₀ (crossBound_nonneg _ _ (gap_pos P.a_small)) (by positivity [P.a_pos])).mpr P.cross_bound
    _ = _ := by ring

theorem Parameters.moment_error (P : Parameters) (f : DomainL2 P.body.domain) :
    ‖P.moment (staticResponse P.body f) - P.moment (P.A f) - P.moment (P.A (P.C (P.A f)))‖ ≤
      Real.sqrt (volume.real P.body.domain) * (16 * P.μ ^ 3 * P.a ^ 6) * ‖f‖ := by
  have h := MomentOperator.response_difference_norm_le P.body.domain P.body.finite
    (staticResponse P.body) (P.A + P.A ∘L P.C ∘L P.A) (δ := 16 * P.μ ^ 3 * P.a ^ 6)
    (by convert P.resolvent_error using 1; congr 1; abel) f
  simpa only [Parameters.moment, add_apply, ContinuousLinearMap.comp_apply, map_add, sub_add_eq_sub_sub] using h

theorem Parameters.p0_error (P : Parameters) :
    ‖P.p0 - P.p0b - P.p0c‖ ≤ 192 * Real.pi * P.μ ^ 3 * P.a ^ 9 := by
  have h := P.moment_error P.f0
  change ‖P.p0 - P.p0b - P.p0c‖ ≤ _ at h
  rw [P.f0_norm] at h
  have heq : Real.sqrt (volume.real P.body.domain) * (16 * P.μ ^ 3 * P.a ^ 6) *
      Real.sqrt (volume.real P.body.domain) = 192 * Real.pi * P.μ ^ 3 * P.a ^ 9 := by
    calc
      _ = (16 * P.μ ^ 3 * P.a ^ 6) * (Real.sqrt (volume.real P.body.domain)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt measureReal_nonneg, P.body_volume]; ring
  exact heq ▸ h

theorem Parameters.p1_error (P : Parameters) :
    ‖P.p1 - P.p1b - P.p1c‖ ≤ (576 * Real.pi / 5) * P.μ ^ 3 * P.a ^ 9 := by
  have h := P.moment_error P.f1
  change ‖P.p1 - P.p1b - P.p1c‖ ≤ _ at h
  apply h.trans
  calc
    _ ≤ Real.sqrt (volume.real P.body.domain) * (16 * P.μ ^ 3 * P.a ^ 6) *
        ((3 / 5) * Real.sqrt (volume.real P.body.domain)) := by gcongr <;> first | exact P.f1_norm | positivity [P.μ_pos, P.a_pos]
    _ = (48 / 5 * P.μ ^ 3 * P.a ^ 6) * (Real.sqrt (volume.real P.body.domain)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt measureReal_nonneg, P.body_volume]; ring


theorem Parameters.p1_norm (P : Parameters) :
    ‖P.p1‖ ≤ (36 * Real.pi / 5) * P.μ * P.a ^ 3 := by
  have hm := MomentOperator.norm_le P.body.domain P.body.finite (staticResponse P.body P.f1)
  change ‖P.p1‖ ≤ Real.sqrt (volume.real P.body.domain) * ‖staticResponse P.body P.f1‖ at hm
  apply hm.trans
  calc
    _ ≤ Real.sqrt (volume.real P.body.domain) * (P.μ * ((3 / 5) * Real.sqrt (volume.real P.body.domain))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact ((staticResponse P.body).le_opNorm P.f1).trans
        (mul_le_mul P.static_norm P.f1_norm (norm_nonneg _) P.μ_pos.le)
    _ = (3 / 5 * P.μ) * (Real.sqrt (volume.real P.body.domain)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt measureReal_nonneg, P.body_volume]; ring

theorem Parameters.p0b_norm (P : Parameters) : ‖P.p0b‖ ≤ 12 * Real.pi * P.μ * P.a ^ 3 := by
  rw [P.p0b_formula, norm_smul, P.electric_norm, mul_one, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [P.a_pos] : 0 ≤ 12 * Real.pi * P.a ^ 3)]
  calc
    _ ≤ P.μ * (12 * Real.pi * P.a ^ 3) := by
      exact mul_le_mul_of_nonneg_right (HomogeneousScalars.beta_norm_le_mu P.μ_pos.le)
        (by positivity [P.a_pos])
    _ = _ := by ring

theorem Parameters.p0c_norm (P : Parameters) : ‖P.p0c‖ ≤ (64 * Real.pi / 9) * P.μ ^ 2 * P.a ^ 6 := by
  rw [P.p0c_formula, norm_smul, P.electric_norm, mul_one]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 64 * Real.pi / 9),
    abs_of_nonneg (by positivity [P.a_pos] : 0 ≤ P.a)]
  gcongr
  exact HomogeneousScalars.beta_norm_le_mu P.μ_pos.le

theorem Parameters.approx0_norm (P : Parameters) :
    ‖P.p0b + P.p0c‖ ≤ 12 * Real.pi * P.μ * P.a ^ 3 + (64 * Real.pi / 9) * P.μ ^ 2 * P.a ^ 6 :=
  (norm_add_le _ _).trans (add_le_add P.p0b_norm P.p0c_norm)

theorem Parameters.p1_difference (P : Parameters) :
    ‖P.p1 - P.p1b‖ ≤ affineCoefficient * P.μ ^ 2 * P.a ^ 8 + (576 * Real.pi / 5) * P.μ ^ 3 * P.a ^ 9 := by
  have h : P.p1 - P.p1b = P.p1c + (P.p1 - P.p1b - P.p1c) := by abel
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add P.p1c_norm P.p1_error)

end QuarticMaxwell.HomogeneousMoments
