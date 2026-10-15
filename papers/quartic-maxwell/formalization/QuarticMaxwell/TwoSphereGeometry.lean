import QuarticMaxwell.TwoSupportBounds
import QuarticMaxwell.FixedPatternWork
import QuarticMaxwell.Certificates

/-! Literal unequal spheres from the dated quartic manuscript. Geometry,
volumes, separated static interaction and physical medium are actual objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell.TwoSphereGeometry
open OQ7Prescribed SphereStatic SphereResponse TwoSupportStatic TwoSupportBounds MeasureTheory Set
variable (n : UnitSphere)

def leftCenter : OQ7Prescribed.Position := (-1 / 2 : ℝ) • (n : OQ7Prescribed.Position)
def rightCenter : OQ7Prescribed.Position := (1 / 2 : ℝ) • (n : OQ7Prescribed.Position)

def leftBall (a : ℝ) : Set OQ7Prescribed.Position := Metric.ball (leftCenter n) a
def rightBall (a : ℝ) : Set OQ7Prescribed.Position := Metric.ball (rightCenter n) (2 * a)
def domain (a : ℝ) : Set OQ7Prescribed.Position := leftBall n a ∪ rightBall n a
def gap (a : ℝ) : ℝ := 1 - 3 * a

theorem leftCenter_norm : ‖(leftCenter n)‖ = (1 / 2 : ℝ) := by simp [leftCenter, norm_smul]
theorem rightCenter_norm : ‖(rightCenter n)‖ = (1 / 2 : ℝ) := by simp [rightCenter, norm_smul]
theorem center_distance : ‖(leftCenter n) - (rightCenter n)‖ = 1 := by
  rw [leftCenter, rightCenter, ← sub_smul]
  norm_num [norm_smul]

theorem gap_pos {a : ℝ} (ha : a ≤ 1 / 20) : 0 < gap a := by unfold gap; linarith

theorem sphere_separation (a : ℝ) :
    ∀ x ∈ leftBall n a, ∀ y ∈ rightBall n a, gap a ≤ ‖x - y‖ := by
  intro x hx y hy
  have hl : ‖x - (leftCenter n)‖ < a := by simpa only [leftBall, Metric.mem_ball, dist_eq_norm] using hx
  have hr : ‖y - (rightCenter n)‖ < 2 * a := by simpa only [rightBall, Metric.mem_ball, dist_eq_norm] using hy
  have ht : ‖(leftCenter n) - (rightCenter n)‖ ≤ ‖x - (leftCenter n)‖ + ‖x - y‖ + ‖y - (rightCenter n)‖ := by
    calc
      _ = ‖((leftCenter n) - x) + (x - y) + (y - (rightCenter n))‖ := by congr 1; abel
      _ ≤ ‖(leftCenter n) - x‖ + ‖x - y‖ + ‖y - (rightCenter n)‖ := by
        apply (norm_add_le _ _).trans
        gcongr
        exact norm_add_le _ _
      _ = _ := by rw [norm_sub_rev (leftCenter n) x]
  rw [center_distance n] at ht
  unfold gap
  linarith

theorem sphere_disjoint {a : ℝ} (ha : a ≤ 1 / 20) : Disjoint (leftBall n a) (rightBall n a) :=
  gap_disjoint _ _ (gap_pos ha) (sphere_separation n a)

theorem left_subset {a : ℝ} (ha : a ≤ 1 / 20) :
    leftBall n a ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) (3 / 5) := by
  intro x hx
  have h := ball_support_bound (leftCenter n) a hx
  rw [leftCenter_norm n] at h
  simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
  linarith

theorem right_subset {a : ℝ} (ha : a ≤ 1 / 20) :
    rightBall n a ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) (3 / 5) := by
  intro x hx
  have h := ball_support_bound (rightCenter n) (2 * a) hx
  rw [rightCenter_norm n] at h
  simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
  linarith

theorem domain_subset {a : ℝ} (ha : a ≤ 1 / 20) :
    domain n a ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) (3 / 5) :=
  union_subset (left_subset n ha) (right_subset n ha)

theorem domain_finite (a : ℝ) : volume (domain n a) ≠ ⊤ :=
  ne_of_lt ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr
    ⟨(ball_measure_ne_top (leftCenter n) a).lt_top, (ball_measure_ne_top (rightCenter n) (2 * a)).lt_top⟩))

theorem left_volume {a : ℝ} (ha : 0 ≤ a) :
    volume.real (leftBall n a) = 4 * Real.pi * a ^ 3 / 3 := ball_volume_real (leftCenter n) ha

theorem right_volume {a : ℝ} (ha : 0 ≤ a) :
    volume.real (rightBall n a) = 32 * Real.pi * a ^ 3 / 3 := by
  rw [rightBall, ball_volume_real (rightCenter n) (by positivity : 0 ≤ 2 * a)]
  ring

theorem domain_volume {a : ℝ} (ha : 0 ≤ a) (hsmall : a ≤ 1 / 20) :
    volume.real (domain n a) = 12 * Real.pi * a ^ 3 := by
  rw [domain, measureReal_union (sphere_disjoint n hsmall) measurableSet_ball
    (ball_measure_ne_top (leftCenter n) a) (ball_measure_ne_top (rightCenter n) (2 * a)),
    left_volume n ha, right_volume n ha]
  ring

theorem crossBound_formula {a : ℝ} (ha : 0 < a) (_hsmall : a ≤ 1 / 20) :
    crossBound (leftBall n a) (rightBall n a) (gap a) =
      4 * Real.sqrt 2 * a ^ 3 / (3 * (gap a) ^ 3) := by
  unfold crossBound
  rw [left_volume n ha.le, right_volume n ha.le]
  have hs : Real.sqrt ((4 * Real.pi * a ^ 3 / 3) * (32 * Real.pi * a ^ 3 / 3)) =
      8 * Real.pi * Real.sqrt 2 * a ^ 3 / 3 := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith only [h2]
  rw [hs]
  field_simp [Real.pi_ne_zero]
  ring


def heterogeneous : ScalarPair where
  left := Complex.I
  right := 2 * Complex.I
  left_loss := by simp
  right_loss := by norm_num

theorem heterogeneous_rho : isolatedRho heterogeneous = 2 := by
  norm_num [isolatedRho, heterogeneous, norm_mul]

theorem fixed_coupling : crossBound (leftBall n (1 / 20)) (rightBall n (1 / 20)) (gap (1 / 20)) =
    4 * Real.sqrt 2 / 14739 := by
  rw [crossBound_formula n (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num)]
  norm_num [gap]
  ring

theorem fixed_static_difference :
    ‖response (leftBall n (1 / 20)) (rightBall n (1 / 20)) Metric.isOpen_ball Metric.isOpen_ball heterogeneous -
      blockInverse (leftBall n (1 / 20)) (rightBall n (1 / 20)) measurableSet_ball measurableSet_ball heterogeneous‖ < 1 / 600 := by
  have hc := fixed_coupling n
  have hcsmall := OQ7Quartic.coupling_lt
  have hsmall : isolatedRho heterogeneous *
      crossBound (leftBall n (1 / 20)) (rightBall n (1 / 20)) (gap (1 / 20)) < 1 := by
    rw [heterogeneous_rho, hc]
    linarith
  have h := response_difference_norm_le (leftBall n (1 / 20)) (rightBall n (1 / 20))
    Metric.isOpen_ball Metric.isOpen_ball (ball_measure_ne_top (leftCenter n) (1 / 20))
    (ball_measure_ne_top (rightCenter n) (2 * (1 / 20))) (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (by norm_num : (0 : ℝ) ≤ 3 / 5) (left_subset n (by norm_num)) (right_subset n (by norm_num))
    (gap (1 / 20)) (gap_pos (by norm_num)) (sphere_separation n (1 / 20)) heterogeneous hsmall
  rw [heterogeneous_rho, hc] at h
  apply h.trans_lt
  norm_num only [OfNat.ofNat_ne_zero, not_false_eq_true, ne_eq, pow_two] at h ⊢
  exact OQ7Quartic.delta_lt (by positivity) hcsmall

end QuarticMaxwell.TwoSphereGeometry



namespace QuarticMaxwell.TwoSphereGeometry
open OQ7Prescribed SphereStatic SphereResponse TwoSupportStatic TwoSupportBounds MeasureTheory Set

def medium (n : UnitSphere) (a : ℝ) (ha : 0 < a) (hsmall : a ≤ 1 / 20) (P : ScalarPair) :
    WeakMaterial.Medium where
  domain := domain n a
  measurable := measurableSet_ball.union measurableSet_ball
  radius := 3 / 5
  radius_nonneg := le_trans ha.le (by linarith : a ≤ 3 / 5)
  subset_ball := domain_subset n hsmall
  finite := domain_finite n a
  susceptibility := susceptibility (leftBall n a) P
  measurable_susceptibility := susceptibility_measurable (leftBall n a) measurableSet_ball P
  M := P.cap
  M_pos := P.cap_pos
  cap := susceptibility_cap (leftBall n a) (rightBall n a) P
  m := P.loss
  m_pos := P.loss_pos
  loss := susceptibility_loss (leftBall n a) (rightBall n a) P

theorem response_eq_staticResponse (n : UnitSphere) (a : ℝ) (ha : 0 < a) (hsmall : a ≤ 1 / 20)
    (P : ScalarPair) :
    response (leftBall n a) (rightBall n a) Metric.isOpen_ball Metric.isOpen_ball P =
      FixedPatternWork.staticResponse (medium n a ha hsmall P) := rfl

theorem medium_volume (n : UnitSphere) (a : ℝ) (ha : 0 < a) (hsmall : a ≤ 1 / 20) (P : ScalarPair) :
    volume.real (medium n a ha hsmall P).domain = 12 * Real.pi * a ^ 3 :=
  domain_volume n ha.le hsmall

theorem medium_volume_pos (n : UnitSphere) (a : ℝ) (ha : 0 < a) (hsmall : a ≤ 1 / 20) (P : ScalarPair) :
    0 < volume.real (medium n a ha hsmall P).domain := by
  rw [medium_volume]
  positivity

theorem medium_reciprocal (n : UnitSphere) (a : ℝ) (ha : 0 < a) (hsmall : a ≤ 1 / 20) (P : ScalarPair) :
    ∀ᵐ x ∂volume, x ∈ (medium n a ha hsmall P).domain → ∀ u v : Vector,
      bilinear u ((medium n a ha hsmall P).susceptibility x v) =
        bilinear v ((medium n a ha hsmall P).susceptibility x u) := by
  classical
  filter_upwards [SphereResponse.scalar_reciprocal P.left (domain n a),
    SphereResponse.scalar_reciprocal P.right (domain n a)] with x hl hr hx u v
  by_cases hm : x ∈ leftBall n a
  · simpa [medium, susceptibility, Set.piecewise, hm] using hl hx u v
  · simpa [medium, susceptibility, Set.piecewise, hm] using hr hx u v

end QuarticMaxwell.TwoSphereGeometry
