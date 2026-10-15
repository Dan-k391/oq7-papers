import QuarticMaxwell.PhysicalPowers
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.ConstMulAction

/-! Actual change of variables for dilated Maxwell media.  The Jacobian,
weak curl and radiation condition are proved from their field definitions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
namespace PhysicalDilation
open MeasureTheory Set OQ7Prescribed

def scaleEquiv (a : ℝ) (ha : a ≠ 0) : Position ≃ᵐ Position :=
  (Homeomorph.smul (Units.mk0 a ha)).toMeasurableEquiv

@[simp] theorem scaleEquiv_apply (a : ℝ) (ha : a ≠ 0) (x : Position) :
    scaleEquiv a ha x = a • x := rfl

theorem integral_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) (ha : 0 < a) (f : Position → E) :
    (∫ x, f (a • x)) = (a ^ 3)⁻¹ • ∫ x, f x := by
  have h := integral_map_equiv (μ := volume) (scaleEquiv a ha.ne') f
  change (∫ x, f x ∂Measure.map (fun x : Position => a • x) volume) = _ at h
  rw [Measure.map_addHaar_smul volume ha.ne', integral_smul_measure] at h
  simpa [Position, finrank_euclideanSpace, abs_of_pos (inv_pos.mpr (pow_pos ha 3)),
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (pow_pos ha 3)))] using h.symm

theorem memLp_scale {E : Type*} [NormedAddCommGroup E] (a : ℝ) (ha : a ≠ 0)
    (f : Position → E) (hf : MemLp f 2 volume) :
    MemLp (fun x : Position => f (a • x)) 2 volume := by
  have hh : MemLp f 2 (Measure.map (fun x : Position => a • x) volume) := by
    rw [Measure.map_addHaar_smul volume ha]
    exact hf.smul_measure (by simp)
  exact hh.comp_of_map (measurable_const_smul a).aemeasurable

theorem locallySquareIntegrable_scale (a : ℝ) (ha : a ≠ 0) (F : Field)
    (hF : LocallySquareIntegrable F) :
    LocallySquareIntegrable (fun x => F (a • x)) := by
  intro K hK
  let L := (fun x : Position => a • x) '' K
  have hL : IsCompact L := hK.image (continuous_const_smul a)
  have hg : MemLp (L.indicator F) 2 volume :=
    (memLp_indicator_iff_restrict hL.measurableSet).mpr (hF L hL)
  have hgs := MemLp.restrict K (memLp_scale a ha _ hg)
  apply MemLp.ae_eq _ hgs
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp only [L, indicator_of_mem (mem_image_of_mem _ hx)]

theorem curl_scale (a : ℝ) (φ : Field) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Position) :
    curl (fun y => φ (a • y)) x = a • curl φ (a • x) := by
  have hd := ((hφ.differentiable (by simp)) (a • x)).hasFDerivAt
  have hs := (a • (1 : Position →L[ℝ] Position)).hasFDerivAt (x := x)
  have hc := hd.comp x hs
  have he : fderiv ℝ (fun y => φ (a • y)) x =
      (fderiv ℝ φ (a • x)).comp (a • (1 : Position →L[ℝ] Position)) := hc.fderiv
  ext i
  fin_cases i <;> simp [curl, he, smul_sub]

theorem bilinear_scale_right (a : ℝ) (u v : Vector) :
    bilinear u (a • v) = a • bilinear u v := by
  simpa only [Complex.real_smul, smul_eq_mul] using bilinear_real_smul_right u v a

theorem bilinear_scale_left (a : ℝ) (u v : Vector) :
    bilinear (a • u) v = a • bilinear u v := by
  rw [bilinear_comm, bilinear_scale_right, bilinear_comm v u]

theorem weakCurl_scale (a : ℝ) (ha : 0 < a) (F G : Field) (hFG : HasWeakCurl F G) :
    HasWeakCurl (fun x => F (a • x)) (fun x => a • G (a • x)) := by
  intro φ hφ hc
  let q : Field := fun y => φ (a⁻¹ • y)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := hφ.comp (contDiff_id.const_smul _)
  have hqc : HasCompactSupport q := hc.comp_smul (inv_ne_zero ha.ne')
  have hcurl := hFG q hq hqc
  have hp (x : Position) : curl q (a • x) = a⁻¹ • curl φ x := by
    simpa [q, smul_smul, ha.ne'] using curl_scale a⁻¹ φ hφ (a • x)
  have h1 := integral_scale a ha (fun y => bilinear (F y) (curl q y))
  simp_rw [hp, bilinear_scale_right] at h1
  rw [integral_smul, hcurl] at h1
  have h2 := integral_scale a ha (fun y => bilinear (G y) (q y))
  simp only [q, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h2
  rw [← h2] at h1
  have h3 := congrArg (fun z : ℂ => a • z) h1
  simp only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul] at h3
  simpa only [bilinear_scale_left, integral_smul] using h3

theorem radial_scale (a : ℝ) (ha : 0 < a) (x : Position) :
    ‖a • x‖⁻¹ • (a • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul, mul_inv_rev]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

theorem outgoing_scale (a : ℝ) (ha : 0 < a) (E H : Field) (h : Outgoing E H) :
    Outgoing (fun x => E (a • x)) (fun x => H (a • x)) := by
  intro ε hε
  obtain ⟨ρ, hρ, hh⟩ := h (a * ε) (mul_pos ha hε)
  refine ⟨ρ / a, div_pos hρ ha, ?_⟩
  intro x hx
  have hax : ρ ≤ ‖a • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith [(div_le_iff₀ ha).mp hx]
  have hbound := hh (a • x) hax
  rw [radial_scale a ha, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hbound
  nlinarith

theorem scaled_subset_ball (B : WeakMaterial.Medium) (r : ℝ) (hr : 0 < r) :
    (fun x : Position => r⁻¹ • x) ⁻¹' B.domain ⊆ Metric.closedBall 0 (r * B.radius) := by
  intro x hx
  have hy := B.subset_ball hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hy ⊢
  calc
    ‖x‖ = r * ‖r⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      field_simp
    _ ≤ r * B.radius := mul_le_mul_of_nonneg_left hy hr.le

def medium (B : WeakMaterial.Medium) (r : ℝ) (hr : 0 < r) : WeakMaterial.Medium where
  domain := (fun x : Position => r⁻¹ • x) ⁻¹' B.domain
  measurable := B.measurable.preimage (measurable_const_smul _)
  radius := r * B.radius
  radius_nonneg := mul_nonneg hr.le B.radius_nonneg
  subset_ball := scaled_subset_ball B r hr
  finite := ne_top_of_le_ne_top (isCompact_closedBall (0 : Position) (r * B.radius)).measure_ne_top
    (measure_mono (scaled_subset_ball B r hr))
  susceptibility := fun x => B.susceptibility (r⁻¹ • x)
  measurable_susceptibility := B.measurable_susceptibility.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne'))
  M := B.M
  M_pos := B.M_pos
  cap := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).ae B.cap
  m := B.m
  m_pos := B.m_pos
  loss := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).ae B.loss

theorem currentField_scale (B : WeakMaterial.Medium) (r : ℝ) (hr : 0 < r) (E : Field)
    (x : Position) :
    WeakMaterial.currentField (medium B r hr) (fun y => E (r⁻¹ • y)) x =
      WeakMaterial.currentField B E (r⁻¹ • x) := by
  by_cases hx : r⁻¹ • x ∈ B.domain <;> simp [WeakMaterial.currentField, medium, hx]

theorem phase_scale (k a : ℝ) (n : UnitSphere) (x : Position) :
    radiationPhase k n (a • x) = radiationPhase (k * a) n x := by
  simp [radiationPhase, real_inner_smul_right, mul_assoc]

theorem incident_scale (k a : ℝ) (n : UnitSphere) (e : Vector) (x : Position) :
    incidentWave k n e (a • x) = incidentWave (k * a) n e x := by
  simp only [incidentWave, phase_scale]

theorem magnetic_scale (k a : ℝ) (n : UnitSphere) (e : Vector) (x : Position) :
    incidentMagneticWave k n e (a • x) = incidentMagneticWave (k * a) n e x := by
  simp only [incidentMagneticWave, phase_scale]

theorem factor_scale (r : ℝ) (hr : 0 < r) (k : ℝ) (z : ℂ) (v : Vector) :
    r⁻¹ • ((z * ((k * r : ℝ) : ℂ)) • v) = (z * (k : ℂ)) • v := by
  rw [← smul_assoc, Complex.real_smul]
  congr 1
  push_cast
  field_simp [hr.ne']

/-- Dilating a physical state changes frequency from k r to k. -/
def state (B : WeakMaterial.Medium) (r : ℝ) (hr : 0 < r) (k : ℝ)
    (n : UnitSphere) (e : Vector) (s : WeakMaterial.State B (k * r) n e) :
    WeakMaterial.State (medium B r hr) k n e where
  electric := fun x => s.electric (r⁻¹ • x)
  magnetic := fun x => s.magnetic (r⁻¹ • x)
  electric_L2 := locallySquareIntegrable_scale _ (inv_ne_zero hr.ne') _ s.electric_L2
  magnetic_L2 := locallySquareIntegrable_scale _ (inv_ne_zero hr.ne') _ s.magnetic_L2
  first_curl := by
    have hh := weakCurl_scale r⁻¹ (inv_pos.mpr hr) _ _ s.first_curl
    simpa only [factor_scale r hr k Complex.I] using hh
  second_curl := by
    have hh := weakCurl_scale r⁻¹ (inv_pos.mpr hr) _ _ s.second_curl
    simpa only [factor_scale r hr k (-Complex.I), currentField_scale] using hh
  outgoing := by
    have hh := outgoing_scale r⁻¹ (inv_pos.mpr hr) _ _ s.outgoing
    convert hh using 1 <;> funext x <;>
      simp [Pi.sub_apply, incident_scale, magnetic_scale, hr.ne']

theorem setIntegral_inverse_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (D : Set Position) (hD : MeasurableSet D)
    (r : ℝ) (hr : 0 < r) (f : Position → E) :
    (∫ x in (fun x : Position => r⁻¹ • x) ⁻¹' D, f (r⁻¹ • x)) =
      r ^ 3 • ∫ x in D, f x := by
  calc
    _ = ∫ x, D.indicator f (r⁻¹ • x) := by
      rw [← integral_indicator (hD.preimage (measurable_const_smul _))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : r⁻¹ • x ∈ D <;> simp [hx]
    _ = ((r⁻¹) ^ 3)⁻¹ • ∫ x, D.indicator f x :=
      integral_scale _ (inv_pos.mpr hr) _
    _ = _ := by rw [integral_indicator hD]; simp

theorem absorption_scale (B : WeakMaterial.Medium) (r : ℝ) (hr : 0 < r)
    (k : ℝ) (E : Field) :
    PhysicalPowers.absorption (medium B r hr) k (fun x => E (r⁻¹ • x)) =
      r ^ 2 * PhysicalPowers.absorption B (k * r) E := by
  unfold PhysicalPowers.absorption
  change k * (∫ x in (fun x : Position => r⁻¹ • x) ⁻¹' B.domain,
    inner ℂ (E (r⁻¹ • x)) (B.susceptibility (r⁻¹ • x) (E (r⁻¹ • x)))).im = _
  rw [setIntegral_inverse_scale B.domain B.measurable r hr
    (fun y => inner ℂ (E y) (B.susceptibility y (E y)))]
  simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

theorem extinction_scale (B : WeakMaterial.Medium) (r : ℝ) (hr : 0 < r)
    (k : ℝ) (n : UnitSphere) (e : Vector) (E : Field) :
    PhysicalPowers.extinction (medium B r hr) k n e (fun x => E (r⁻¹ • x)) =
      r ^ 2 * PhysicalPowers.extinction B (k * r) n e E := by
  unfold PhysicalPowers.extinction
  have hi (x : Position) : incidentWave k n e x = incidentWave (k * r) n e (r⁻¹ • x) := by
    simp only [incident_scale, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]
  simp_rw [hi]
  change k * (∫ x in (fun x : Position => r⁻¹ • x) ⁻¹' B.domain,
    inner ℂ (incidentWave (k * r) n e (r⁻¹ • x))
      (B.susceptibility (r⁻¹ • x) (E (r⁻¹ • x)))).im = _
  rw [setIntegral_inverse_scale B.domain B.measurable r hr
    (fun y => inner ℂ (incidentWave (k * r) n e y) (B.susceptibility y (E y)))]
  simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

theorem absorption_congr (B : WeakMaterial.Medium) (k : ℝ) {E F : Field}
    (h : E =ᵐ[volume] F) : PhysicalPowers.absorption B k E = PhysicalPowers.absorption B k F := by
  unfold PhysicalPowers.absorption
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [hx]

theorem extinction_congr (B : WeakMaterial.Medium) (k : ℝ) (n : UnitSphere) (e : Vector)
    {E F : Field} (h : E =ᵐ[volume] F) :
    PhysicalPowers.extinction B k n e E = PhysicalPowers.extinction B k n e F := by
  unfold PhysicalPowers.extinction
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [hx]

theorem state_electric_unique (B : WeakMaterial.Medium) (k : ℝ) (hk : 0 < k)
    (n : UnitSphere) (e : Vector) (he : bilinear (complexify (n : Position)) e = 0)
    (s t : WeakMaterial.State B k n e) : s.electric =ᵐ[volume] t.electric := by
  obtain ⟨u, hu⟩ := WeakMaterial.wellposed B hk n e he
  exact (hu s).1.trans (hu t).1.symm

end PhysicalDilation
end QuarticMaxwell
