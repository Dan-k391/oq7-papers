import GeneralizedResearch.BeamPackets
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The unitary physical inverse Fourier transform in two transverse dimensions.
The standard Mathlib 2π transform is converted to the exp(i κ·x) convention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.PhysicalFourier
open MeasureTheory BeamPackets
open scoped FourierTransform
abbrev Transverse := BeamAveraging.Transverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def scaleEquiv (a : ℝ) (ha : a ≠ 0) : Transverse ≃ᵐ Transverse :=
  (Homeomorph.smul (Units.mk0 a ha)).toMeasurableEquiv

theorem integral_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (a : ℝ) (ha : 0 < a) (f : Transverse → F) :
    (∫ x, f (a • x)) = (a ^ 2)⁻¹ • ∫ x, f x := by
  have h := integral_map_equiv (μ := volume) (scaleEquiv a ha.ne') f
  change (∫ x, f x ∂Measure.map (fun x : Transverse => a • x) volume) = _ at h
  rw [Measure.map_addHaar_smul volume ha.ne', integral_smul_measure] at h
  simpa [scaleEquiv, Transverse, BeamAveraging.Transverse, finrank_euclideanSpace,
    abs_of_pos (inv_pos.mpr (pow_pos ha 2)),
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (pow_pos ha 2)))] using h.symm

omit [InnerProductSpace ℂ E] in
theorem memLp_scale (a : ℝ) (ha : a ≠ 0) (f : Transverse → E) (hf : MemLp f 2 volume) :
    MemLp (fun x : Transverse => f (a • x)) 2 volume := by
  have hh : MemLp f 2 (Measure.map (fun x : Transverse => a • x) volume) := by
    rw [Measure.map_addHaar_smul volume ha]
    exact hf.smul_measure (by simp)
  exact hh.comp_of_map (measurable_const_smul a).aemeasurable

def transport (a : ℝ) (ha : 0 < a) (f : Lp E 2 (volume : Measure Transverse)) :
    Lp E 2 (volume : Measure Transverse) :=
  ((memLp_scale a ha.ne' f (Lp.memLp f)).const_smul (a : ℂ)).toLp
    (fun x => (a : ℂ) • f (a • x))

theorem transport_ae (a : ℝ) (ha : 0 < a) (f : Lp E 2 (volume : Measure Transverse)) :
    (transport a ha f : Transverse → E) =ᵐ[volume] fun x => (a : ℂ) • f (a • x) :=
  ((memLp_scale a ha.ne' f (Lp.memLp f)).const_smul (a : ℂ)).coeFn_toLp

theorem transport_norm_sq (a : ℝ) (ha : 0 < a) (f : Lp E 2 (volume : Measure Transverse)) :
    ‖transport a ha f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← lp_integral_norm_sq]
  have he : (∫ x : Transverse, ‖transport a ha f x‖ ^ 2) =
      a ^ 2 * ∫ x : Transverse, ‖f (a • x)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [transport_ae a ha f] with x hx
    simp only [hx, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  rw [he, integral_scale a ha (fun x => ‖f x‖ ^ 2), smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'), one_mul, lp_integral_norm_sq]

theorem transport_norm (a : ℝ) (ha : 0 < a) (f : Lp E 2 (volume : Measure Transverse)) :
    ‖transport a ha f‖ = ‖f‖ := by
  nlinarith [transport_norm_sq a ha f, norm_nonneg (transport a ha f), norm_nonneg f]

theorem transport_inner (a : ℝ) (ha : 0 < a) (f g : Lp E 2 (volume : Measure Transverse)) :
    inner ℂ (transport a ha f) (transport a ha g) = inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def]
  have he : (∫ x : Transverse, inner ℂ (transport a ha f x) (transport a ha g x)) =
      (a ^ 2 : ℂ) * ∫ x : Transverse, inner ℂ (f (a • x)) (g (a • x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [transport_ae a ha f, transport_ae a ha g] with x hf hg
    rw [hf, hg, inner_smul_left, inner_smul_right]
    simp only [Complex.conj_ofReal]
    ring
  rw [he, integral_scale a ha (fun x => inner ℂ (f x) (g x)), Complex.real_smul]
  rw [← mul_assoc]
  have hc : (a ^ 2 : ℂ) * (((a ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [ha.ne']
  rw [hc, one_mul]

def factor : ℝ := (2 * Real.pi)⁻¹
theorem factor_pos : 0 < factor := by unfold factor; positivity

variable [CompleteSpace E]

def inverse (f : Lp E 2 (volume : Measure Transverse)) : Lp E 2 (volume : Measure Transverse) :=
  transport factor factor_pos (BeamPackets.spatial f)

theorem inverse_norm (f : Lp E 2 (volume : Measure Transverse)) : ‖inverse f‖ = ‖f‖ := by
  rw [inverse, transport_norm, BeamPackets.spatial_norm]

theorem inverse_inner (f g : Lp E 2 (volume : Measure Transverse)) :
    inner ℂ (inverse f) (inverse g) = inner ℂ f g := by
  rw [inverse, inverse, transport_inner, BeamPackets.spatial_inner]

theorem inverse_ae (f : Lp E 2 (volume : Measure Transverse)) :
    (inverse f : Transverse → E) =ᵐ[volume]
      fun x => (factor : ℂ) • (BeamPackets.spatial f) (factor • x) :=
  transport_ae factor factor_pos _

end GeneralizedResearch.PhysicalFourier
