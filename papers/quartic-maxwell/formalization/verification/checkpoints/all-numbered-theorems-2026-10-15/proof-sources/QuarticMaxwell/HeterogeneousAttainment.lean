import QuarticMaxwell.HeterogeneousCertificate
import QuarticMaxwell.HeterogeneousRemainder
import QuarticMaxwell.QuantitativeQuotient
import QuarticMaxwell.FixedPatternDilation

/-! The original finite heterogeneous-sphere theorem for actual outgoing weak
Maxwell states.  The continuum coefficient and the sixth-order remainder are
derived from the interacting volume inverse, with no dipole approximation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace QuarticMaxwell.HeterogeneousAttainment
open MeasureTheory OQ7Prescribed WeakMaterial FixedPatternWork FixedPatternScattering
open FixedPatternContrast PhysicalPowers PhysicalDilation
local notation "B" => HeterogeneousCertificate.body
local notation "w" => HeterogeneousCertificate.volume

theorem denominator_lower (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1)
    (t : ℝ) (ht : 0 < t) (hsmall : t ≤ 1 / 4) :
    w n ≤ forwardWork (B n) t ht n e ∧ w n ≤ D0 (B n) e := by
  have hD := (HeterogeneousCertificate.extinction_interval n e hen).1
  have herror := (HeterogeneousRemainder.physical_errors n e hen t ht).2
  change |forwardWork (B n) t ht n e - D0 (B n) e| ≤ 108 / 25 * w n * t ^ 2 at herror
  have ht2 : t ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith only [ht, hsmall]
  have hw := (HeterogeneousCertificate.volume_pos n).le
  have hE := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 108 / 25 * w n by positivity)
  have hlo := (abs_le.mp herror).1
  constructor <;> nlinarith only [hD, hlo, hE, hw]

theorem leading_bound (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) :
    |leading (B n) n e| ≤ 88 / (2925 * Real.pi) * w n ^ 2 := by
  change |(2 / (3 * Real.pi)) * HeterogeneousCertificate.I0 n e| ≤ _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (3 * Real.pi))]
  calc
    _ ≤ (2 / (3 * Real.pi)) * ((44 / 975) * w n ^ 2) :=
      mul_le_mul_of_nonneg_left (HeterogeneousCertificate.imaginary_moment_interval n e hen).2 (by positivity)
    _ = _ := by ring

theorem remainder_constant_bound (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) :
    (168 / (25 * Real.pi) * w n ^ 2) / w n +
      |leading (B n) n e| * (108 / 25 * w n) / (w n) ^ 2 ≤ 21 / 2000 := by
  have hw := HeterogeneousCertificate.volume_pos n
  calc
    _ ≤ (168 / (25 * Real.pi) * w n ^ 2) / w n +
      (88 / (2925 * Real.pi) * w n ^ 2) * (108 / 25 * w n) / (w n) ^ 2 := by
        gcongr
        exact leading_bound n e hen
    _ = (168 / 25 + (88 / 2925) * (108 / 25)) * (w n / Real.pi) := by
      field_simp [hw.ne', Real.pi_ne_zero]
    _ ≤ _ := by rw [HeterogeneousCertificate.volume_eq]; field_simp [Real.pi_ne_zero]; norm_num

theorem quotient_remainder (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1)
    (t : ℝ) (ht : 0 < t) (hsmall : t ≤ 1 / 4) :
    |t ^ 3 * |signedScattering (B n) t ht n e| / forwardWork (B n) t ht n e -
      coefficient (B n) n e * t ^ 4| ≤ (21 / 2000) * t ^ 6 := by
  have hlower := denominator_lower n e hen t ht hsmall
  have herr := HeterogeneousRemainder.physical_errors n e hen t ht
  change |signedScattering (B n) t ht n e - t * leading (B n) n e| ≤
    168 / (25 * Real.pi) * w n ^ 2 * t ^ 3 ∧
    |forwardWork (B n) t ht n e - D0 (B n) e| ≤ 108 / 25 * w n * t ^ 2 at herr
  have hs : |signedScattering (B n) t ht n e - leading (B n) n e * t| ≤
      168 / (25 * Real.pi) * w n ^ 2 * t ^ 3 := by simpa only [mul_comm] using herr.1
  have h := quartic_quotient_error_of_lower_bound ht.le
    (HeterogeneousCertificate.volume_pos n) hlower.1 hlower.2
    (by positivity : 0 ≤ 168 / (25 * Real.pi) * w n ^ 2)
    (by have hw := (HeterogeneousCertificate.volume_pos n).le; positivity : 0 ≤ 108 / 25 * w n)
    hs herr.2
  exact h.trans (mul_le_mul_of_nonneg_right (remainder_constant_bound n e hen) (by positivity))

/-- The full quantitative statement for every independently supplied weak
outgoing Maxwell state on the actual two finite spheres. -/
theorem finite_sphere_remainder (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (t : ℝ) (ht : 0 < t) (hsmall : t ≤ 1 / 4)
    (s : State (B n) t n e) (r : State (B n) t (opposite n) e) :
    |contrast (B n) t n e s r - coefficient (B n) n e * t ^ 4| ≤
      (21 / 2000) * t ^ 6 := by
  rw [contrast_eq_quotient (B n) t ht
    (TwoSphereGeometry.medium_reciprocal n (1 / 20) (by norm_num) (by norm_num) _)
    n e he htr s r]
  exact quotient_remainder n e hen t ht hsmall

theorem finite_sphere_lower (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (t : ℝ) (ht : 0 < t) (hsmall : t ≤ 1 / 40)
    (s : State (B n) t n e) (r : State (B n) t (opposite n) e) :
    (27 / 1299125) * t ^ 4 ≤ contrast (B n) t n e s r := by
  have h := (abs_le.mp (finite_sphere_remainder n e he hen htr t ht (by linarith) s r)).1
  have hC := mul_le_mul_of_nonneg_right
    (HeterogeneousCertificate.coefficient_interval n e hen).1 (by positivity : 0 ≤ t ^ 4)
  have ht2 : t ^ 2 ≤ (1 / 1600 : ℝ) := by nlinarith only [ht, hsmall]
  have hrem := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ (21 / 2000 : ℝ) * t ^ 4 by positivity)
  have heq : (21 / 2000 : ℝ) * t ^ 4 * t ^ 2 = (21 / 2000 : ℝ) * t ^ 6 := by ring
  rw [heq] at hrem
  nlinarith only [h, hC, hrem, (by positivity : 0 ≤ t ^ 4)]

/-- Literal fixed-physical-wavenumber shrinking-body version of Theorem 1.2.
All powers refer to the actual dilated weak Maxwell fields. -/
theorem fixed_wavenumber_remainder (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (r : ℝ) (hr : 0 < r) (hsmall : k * r ≤ 1 / 4)
    (s : State (PhysicalDilation.medium (B n) r hr) k n e)
    (q : State (PhysicalDilation.medium (B n) r hr) k (opposite n) e) :
    |contrast (PhysicalDilation.medium (B n) r hr) k n e s q -
      coefficient (B n) n e * (k * r) ^ 4| ≤ (21 / 2000) * (k * r) ^ 6 := by
  have hkr := mul_pos hk hr
  let s0 := solution (B n) (k * r) hkr n e htr
  let q0 := solution (B n) (k * r) hkr (opposite n) e (PhysicalPowers.opposite_transverse n e htr)
  have hs := state_electric_unique (PhysicalDilation.medium (B n) r hr) k hk n e htr s
    (PhysicalDilation.state (B n) r hr k n e s0)
  have hq := state_electric_unique (PhysicalDilation.medium (B n) r hr) k hk (opposite n) e
    (PhysicalPowers.opposite_transverse n e htr) q (PhysicalDilation.state (B n) r hr k (opposite n) e q0)
  rw [FixedPatternDilation.contrast_congr _ _ _ _ s _ q _ hs hq, FixedPatternDilation.contrast_scale]
  exact finite_sphere_remainder n e he hen htr (k * r) hkr hsmall s0 q0

theorem fixed_wavenumber_lower (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (r : ℝ) (hr : 0 < r) (hsmall : k * r ≤ 1 / 40)
    (s : State (PhysicalDilation.medium (B n) r hr) k n e)
    (q : State (PhysicalDilation.medium (B n) r hr) k (opposite n) e) :
    (27 / 1299125) * (k * r) ^ 4 ≤ contrast (PhysicalDilation.medium (B n) r hr) k n e s q := by
  have h := (abs_le.mp (fixed_wavenumber_remainder k hk n e he hen htr r hr (by linarith) s q)).1
  have hC := mul_le_mul_of_nonneg_right
    (HeterogeneousCertificate.coefficient_interval n e hen).1 (by positivity : 0 ≤ (k * r) ^ 4)
  have ht := mul_pos hk hr
  have ht2 : (k * r) ^ 2 ≤ (1 / 1600 : ℝ) := by nlinarith only [ht, hsmall]
  have hrem := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ (21 / 2000 : ℝ) * (k * r) ^ 4 by positivity)
  have heq : (21 / 2000 : ℝ) * (k * r) ^ 4 * (k * r) ^ 2 = (21 / 2000 : ℝ) * (k * r) ^ 6 := by ring
  rw [heq] at hrem
  nlinarith only [h, hC, hrem, (by positivity : 0 ≤ (k * r) ^ 4)]

end QuarticMaxwell.HeterogeneousAttainment
