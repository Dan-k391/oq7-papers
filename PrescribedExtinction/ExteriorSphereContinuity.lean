import PrescribedExtinction.WeakCurlProducts
import PrescribedExtinction.ExteriorOutgoing

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem outgoingRadialSecond_continuousAt (k r : ℝ) (hr : r ≠ 0) :
    ContinuousAt (outgoingRadialSecond k) r := by
  have hR : ContinuousAt (fun s : ℝ => (s : ℂ)) r := Complex.continuous_ofReal.continuousAt
  have hC : ContinuousAt (fun s : ℝ => Complex.I * (k : ℂ) * (s : ℂ)) r := continuousAt_const.mul hR
  have hden : (((4 * Real.pi : ℝ) : ℂ) * (r : ℂ) ^ 3) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hr))
  exact (hC.cexp.mul (((hC.pow 2).sub (continuousAt_const.mul hC)).add continuousAt_const)).div
    (continuousAt_const.mul (hR.pow 3)) hden

theorem classicalDyadic_apply_continuousAt (k : ℝ) (x : Position) (hx : x ≠ 0) (v : Vector) :
    ContinuousAt (fun y => classicalDyadic k y v) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnC : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hnorm : ContinuousAt (fun y : Position => (‖y‖ : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt
  have h0 : ContinuousAt (fun y => outgoingRadial k ‖y‖) x :=
    (outgoingRadial_hasDerivAt k ‖x‖ hn).continuousAt.comp continuous_norm.continuousAt
  have h1 : ContinuousAt (fun y => outgoingRadialFirst k ‖y‖) x :=
    (outgoingRadialFirst_hasDerivAt k ‖x‖ hn).continuousAt.comp continuous_norm.continuousAt
  have h2 : ContinuousAt (fun y => outgoingRadialSecond k ‖y‖) x :=
    (outgoingRadialSecond_continuousAt k ‖x‖ hn).comp continuous_norm.continuousAt
  have hrank : ContinuousAt (fun y : Position => inner ℂ (complexify y) v • complexify y) x :=
    (complexify_continuous.continuousAt.inner (𝕜 := ℂ) (continuousAt_const (y := v))).smul
      complexify_continuous.continuousAt
  simp only [classicalDyadic, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply]
  exact (((continuousAt_const.mul h0).add (h1.div hnorm hnC)).smul continuousAt_const).add
    (((h2.div (hnorm.pow 2) (pow_ne_zero 2 hnC)).sub
      (h1.div (hnorm.pow 3) (pow_ne_zero 3 hnC))).smul hrank)

theorem kernelMagnetic_apply_continuousAt (k : ℝ) (x : Position) (hx : x ≠ 0) (v : Vector) :
    ContinuousAt (fun y => kernelMagnetic k y v) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : ContinuousAt (fun y : Position => (‖y‖ : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt
  have h1 : ContinuousAt (fun y => outgoingRadialFirst k ‖y‖) x :=
    (outgoingRadialFirst_hasDerivAt k ‖x‖ hn).continuousAt.comp continuous_norm.continuousAt
  exact ((continuousAt_const.mul h1).div hnorm (Complex.ofReal_ne_zero.mpr hn)).smul
    (cross_continuous_fields complexify (fun _ => v) complexify_continuous continuous_const).continuousAt

theorem sphere_displaced_norm_ge_one (p : CompactPolarization) (r : ℝ)
    (hr : 2 * p.radius + 2 ≤ r) (n : UnitSphere) (y : Position) (hy : ‖y‖ ≤ p.radius) :
    1 ≤ ‖r • (n : Position) - y‖ := by
  have hrpos : 0 < r := by linarith [p.radius_nonneg]
  have hnorm : ‖r • (n : Position)‖ = r := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, unitSphere_norm]
  have htri := norm_sub_norm_le (r • (n : Position)) y
  rw [hnorm] at htri
  linarith [p.radius_nonneg]

theorem exteriorElectric_sphere_continuous (k : ℝ) (p : CompactPolarization)
    (r : ℝ) (hr : 2 * p.radius + 2 ≤ r) :
    Continuous (fun n : UnitSphere => exteriorElectric k p (r • (n : Position))) := by
  have hrpos : 0 < r := by linarith [p.radius_nonneg]
  have hnorm (n : UnitSphere) : ‖r • (n : Position)‖ = r := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, unitSphere_norm]
  unfold exteriorElectric
  apply continuous_of_dominated (bound := fun y : Position => exteriorKernelBound k * ‖p.current y‖)
  · intro n
    exact (exteriorElectric_integrable_far k p _ (by rw [hnorm]; linarith [p.radius_nonneg])).aestronglyMeasurable
  · intro n
    apply ae_of_all
    intro y
    by_cases hy : ‖y‖ ≤ p.radius
    · exact classicalDyadic_norm_le_far k _ (sphere_displaced_norm_ge_one p r hr n y hy) _
    · rw [p.vanish y (lt_of_not_ge hy), map_zero, norm_zero, mul_zero]
  · exact (compactPolarization_current_integrable p).norm.const_mul _
  · apply ae_of_all
    intro y
    by_cases hy : ‖y‖ ≤ p.radius
    · apply continuous_iff_continuousAt.mpr
      intro n
      have hn : r • (n : Position) - y ≠ 0 := norm_pos_iff.mp (by
        have h := sphere_displaced_norm_ge_one p r hr n y hy; linarith)
      have hdis : ContinuousAt (fun m : UnitSphere => r • (m : Position) - y) n :=
        (((continuous_subtype_val : Continuous (fun m : UnitSphere => (m : Position))).const_smul r).sub continuous_const).continuousAt
      exact (classicalDyadic_apply_continuousAt k _ hn (p.current y)).comp' (f := fun m : UnitSphere => r • (m : Position) - y) (x := n) hdis
    · have he : (fun n : UnitSphere => classicalDyadic k (r • (n : Position) - y) (p.current y)) =
          fun _ => (0 : Vector) := by funext n; rw [p.vanish y (lt_of_not_ge hy), map_zero]
      rw [he]
      exact continuous_const

theorem exteriorMagnetic_sphere_continuous (k : ℝ) (p : CompactPolarization)
    (r : ℝ) (hr : 2 * p.radius + 2 ≤ r) :
    Continuous (fun n : UnitSphere => exteriorMagnetic k p (r • (n : Position))) := by
  have hrpos : 0 < r := by linarith [p.radius_nonneg]
  have hnorm (n : UnitSphere) : ‖r • (n : Position)‖ = r := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, unitSphere_norm]
  unfold exteriorMagnetic
  apply continuous_of_dominated (bound := fun y : Position =>
    (|k| * (|k| + 1) / (4 * Real.pi)) * ‖p.current y‖)
  · intro n
    exact (exteriorMagnetic_integrable_far k p _ (by rw [hnorm]; linarith [p.radius_nonneg])).aestronglyMeasurable
  · intro n
    apply ae_of_all
    intro y
    by_cases hy : ‖y‖ ≤ p.radius
    · exact kernelMagnetic_norm_le_far k _ (sphere_displaced_norm_ge_one p r hr n y hy) _
    · simp [p.vanish y (lt_of_not_ge hy), kernelMagnetic, cross]
  · exact (compactPolarization_current_integrable p).norm.const_mul _
  · apply ae_of_all
    intro y
    by_cases hy : ‖y‖ ≤ p.radius
    · apply continuous_iff_continuousAt.mpr
      intro n
      have hn : r • (n : Position) - y ≠ 0 := norm_pos_iff.mp (by
        have h := sphere_displaced_norm_ge_one p r hr n y hy; linarith)
      have hdis : ContinuousAt (fun m : UnitSphere => r • (m : Position) - y) n :=
        (((continuous_subtype_val : Continuous (fun m : UnitSphere => (m : Position))).const_smul r).sub continuous_const).continuousAt
      exact (kernelMagnetic_apply_continuousAt k _ hn (p.current y)).comp' (f := fun m : UnitSphere => r • (m : Position) - y) (x := n) hdis
    · have he : (fun n : UnitSphere => kernelMagnetic k (r • (n : Position) - y) (p.current y)) =
          fun _ => (0 : Vector) := by funext n; simp [p.vanish y (lt_of_not_ge hy), kernelMagnetic, cross]
      rw [he]
      exact continuous_const

end OQ7Prescribed
