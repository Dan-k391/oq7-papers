import QuarticMaxwell.TwoSphereGeometry
import QuarticMaxwell.FixedPatternContrast

/-! Quantitative full-Maxwell remainder bounds for the actual fixed
heterogeneous two-sphere medium.  No dipole response is substituted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.HeterogeneousRemainder
open MeasureTheory OQ7Prescribed WeakMaterial FixedPatternWork FixedPatternScattering FixedPatternContrast

def body (n : UnitSphere) : Medium :=
  TwoSphereGeometry.medium n (1 / 20) (by norm_num) (by norm_num) TwoSphereGeometry.heterogeneous

def w (n : UnitSphere) : ℝ := volume.real (body n).domain

theorem w_pos (n : UnitSphere) : 0 < w n :=
  TwoSphereGeometry.medium_volume_pos n _ _ _ _

theorem w_formula (n : UnitSphere) : w n = 3 * Real.pi / 2000 := by
  rw [w, body, TwoSphereGeometry.medium_volume]
  ring

theorem rho_eq (n : UnitSphere) : rho (body n) = 4 := by
  norm_num [rho, body, TwoSphereGeometry.medium, TwoSupportStatic.ScalarPair.cap,
    TwoSupportStatic.ScalarPair.loss, TwoSphereGeometry.heterogeneous, norm_mul]

theorem radius_eq (n : UnitSphere) : (body n).radius = 3 / 5 := rfl

theorem source_norm_sq (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) :
    ‖constantInput (body n) e‖ ^ 2 = w n := by
  rw [constantInput, SourceTaylor.constant_norm_sq _ _ _ n e, hen, one_pow, mul_one]
  rfl

theorem volumeRadius_cube_eq (n : UnitSphere) : volumeRadius (w n) ^ 3 = 9 / 8000 := by
  rw [volumeRadius_cube (w_pos n).le, w_formula]
  field_simp
  norm_num

theorem volumeRadius_le (n : UnitSphere) : volumeRadius (w n) ≤ 3 / 25 := by
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by norm_num)
  rw [volumeRadius_cube_eq]
  norm_num

theorem correction_le (n : UnitSphere) : correction (body n) ≤ 9 / 50 := by
  have hA := volumeRadius_pos (w_pos n)
  have hsq : volumeRadius (w n) ^ 2 ≤ (3 / 25 : ℝ) ^ 2 :=
    (sq_le_sq₀ hA.le (by norm_num)).mpr (volumeRadius_le n)
  unfold correction
  rw [rho_eq]
  change 3 / 4 * 4 ^ 2 * volumeRadius (w n) ^ 2 ≤ _
  nlinarith only [hsq]

theorem cosineError_le (n : UnitSphere) :
    rho (body n) * (body n).radius ^ 2 / 2 + correction (body n) ≤ 9 / 10 := by
  rw [rho_eq, radius_eq]
  linarith [correction_le n]

theorem sineError_le (n : UnitSphere) :
    rho (body n) * (body n).radius ^ 3 / 6 + correction (body n) * (body n).radius ≤ 63 / 250 := by
  rw [rho_eq, radius_eq]
  linarith [correction_le n]

theorem gramCorrection_eq (n : UnitSphere) : gramCorrection (body n) = 3 * w n / (25 * Real.pi) := by
  unfold gramCorrection
  rw [radius_eq]
  change w n * (3 / 5) ^ 2 / (3 * Real.pi) = _
  ring

theorem errorConstant_le (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) :
    errorConstant (body n) e ≤ 168 / (25 * Real.pi) * w n ^ 2 := by
  have hw := (w_pos n).le
  have hU := cosineError_le n
  have hV := sineError_le n
  have hρ := (rho_pos (body n)).le
  have hR := (body n).radius_nonneg
  have hG : 0 ≤ gramBound (body n) := by unfold gramBound; positivity
  unfold errorConstant
  rw [source_norm_sq n e hen]
  calc
    _ ≤ 4 * w n *
      ((9 / 10) * gramBound (body n) * rho (body n) * (body n).radius +
        rho (body n) ^ 2 * gramCorrection (body n) * (body n).radius +
        rho (body n) * gramBound (body n) * (63 / 250)) := by
      gcongr
    _ = _ := by
      rw [rho_eq, radius_eq, gramCorrection_eq]
      unfold gramBound
      change 4 * w n * ((9 / 10) * (w n / (6 * Real.pi)) * 4 * (3 / 5) +
        4 ^ 2 * (3 * w n / (25 * Real.pi)) * (3 / 5) +
        4 * (w n / (6 * Real.pi)) * (63 / 250)) = _
      ring

theorem denominatorError_le (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) :
    denominatorError (body n) e ≤ 108 / 25 * w n := by
  unfold denominatorError
  rw [source_norm_sq n e hen, rho_eq, radius_eq]
  have hC := mul_le_mul_of_nonneg_left (correction_le n) (w_pos n).le
  nlinarith only [hC, (w_pos n).le]

theorem physical_errors (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1)
    (t : ℝ) (ht : 0 < t) :
    |signedScattering (body n) t ht n e - t * leading (body n) n e| ≤
        168 / (25 * Real.pi) * w n ^ 2 * t ^ 3 ∧
      |forwardWork (body n) t ht n e - D0 (body n) e| ≤ 108 / 25 * w n * t ^ 2 := by
  constructor
  · simpa only [mul_comm] using (signedScattering_error (body n) (w_pos n) t ht n e).trans
      (mul_le_mul_of_nonneg_right (errorConstant_le n e hen) (by positivity))
  · exact (forward_work_error (body n) (w_pos n) t ht n e).trans
      (mul_le_mul_of_nonneg_right (denominatorError_le n e hen) (sq_nonneg t))

end QuarticMaxwell.HeterogeneousRemainder
