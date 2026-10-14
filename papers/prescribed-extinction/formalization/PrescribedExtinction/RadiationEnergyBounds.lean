import PrescribedExtinction.OutgoingSourceFields
import PrescribedExtinction.TensorLossCoercivity
import PrescribedExtinction.SmoothOutgoingFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

def magneticDecayConstant (k : ℝ) : ℝ := 2 * (|k| * (|k| + 1) / (4 * Real.pi))

theorem kernelMagnetic_norm_decay (k : ℝ) (x : Position) (hx : 1 ≤ ‖x‖) (v : Vector) :
    ‖kernelMagnetic k x v‖ ≤ (|k| * (|k| + 1) / (4 * Real.pi) / ‖x‖) * ‖v‖ := by
  have hn : x ≠ 0 := norm_pos_iff.mp (by linarith)
  apply (kernelMagnetic_norm_le k x hn v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  calc
    _ ≤ |k| * ((|k| + 1) * ‖x‖) / (4 * Real.pi * ‖x‖ ^ 2) := by
      gcongr
      nlinarith [abs_nonneg k]
    _ = _ := by field_simp

theorem displaced_kernelMagnetic_norm_decay (k R : ℝ) (hR : 0 ≤ R)
    (x y : Position) (hx : 2 * R + 2 ≤ ‖x‖) (hy : ‖y‖ ≤ R) (v : Vector) :
    ‖kernelMagnetic k (x - y) v‖ ≤ magneticDecayConstant k / ‖x‖ * ‖v‖ := by
  have hs : 1 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
  have hh : ‖x‖ / 2 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
  have hn : 0 < ‖x‖ := by linarith
  apply (kernelMagnetic_norm_decay k (x - y) hs v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  calc
    _ ≤ (|k| * (|k| + 1) / (4 * Real.pi)) / (‖x‖ / 2) := by gcongr
    _ = _ := by unfold magneticDecayConstant; field_simp

theorem exteriorMagnetic_norm_decay (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : 2 * p.radius + 2 ≤ ‖x‖) :
    ‖exteriorMagnetic k p x‖ ≤ magneticDecayConstant k / ‖x‖ * ∫ y : Position, ‖p.current y‖ := by
  calc
    _ ≤ ∫ y : Position, (magneticDecayConstant k / ‖x‖) * ‖p.current y‖ := by
      apply norm_integral_le_of_norm_le ((compactPolarization_current_integrable p).norm.const_mul _)
      apply ae_of_all
      intro y
      by_cases hy : ‖y‖ ≤ p.radius
      · exact displaced_kernelMagnetic_norm_decay k p.radius p.radius_nonneg x y hx hy _
      · simp [kernelMagnetic, cross, p.vanish y (lt_of_not_ge hy)]
    _ = _ := integral_const_mul _ _

theorem poynting_flux_lower_bound (E H : Vector) (n : Position) (hn : ‖n‖ = 1) :
    -(‖H‖ * ‖cross H (complexify n) - E‖) ≤
      (pairing E (cross H (complexify n))).re := by
  let C := cross H (complexify n)
  let D := C - E
  have hC : ‖C‖ ≤ ‖H‖ := by
    simpa [C, complexify_norm, hn] using cross_norm_le H (complexify n)
  have hE : E = C - D := by dsimp [D]; abel
  have hp := (Complex.re_le_norm (inner ℂ D C)).trans (norm_inner_le_norm D C)
  have hm : ‖D‖ * ‖C‖ ≤ ‖H‖ * ‖D‖ := by nlinarith [norm_nonneg D]
  rw [pairing_eq_inner]
  change -(‖H‖ * ‖D‖) ≤ (inner ℂ E C).re
  rw [hE, inner_sub_left, Complex.sub_re]
  have hs : (inner ℂ C C).re = ‖C‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) C
  rw [hs]
  nlinarith [sq_nonneg ‖C‖]

theorem exterior_poynting_flux_lower_bound (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : 2 * p.radius + 2 ≤ ‖x‖) :
    -((magneticDecayConstant k / ‖x‖ * ∫ y : Position, ‖p.current y‖) *
      (radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖)) ≤
      (pairing (exteriorElectric k p x)
        (cross (exteriorMagnetic k p x) (complexify (radialDirection x)))).re := by
  have hn : x ≠ 0 := norm_pos_iff.mp (by linarith [p.radius_nonneg])
  have hh := exteriorMagnetic_norm_decay k p x hx
  have hd := exterior_radiation_integral_norm_le k p x hx
  have hconst : 0 ≤ magneticDecayConstant k := by unfold magneticDecayConstant; positivity
  have hint : 0 ≤ ∫ y : Position, ‖p.current y‖ := integral_nonneg (fun y => norm_nonneg (p.current y))
  have ha : 0 ≤ magneticDecayConstant k / ‖x‖ * ∫ y : Position, ‖p.current y‖ :=
    mul_nonneg (div_nonneg hconst (norm_nonneg x)) hint
  have hm := mul_le_mul hh hd (norm_nonneg
    (cross (exteriorMagnetic k p x) (complexify (radialDirection x)) - exteriorElectric k p x)) ha
  exact (neg_le_neg hm).trans
    (poynting_flux_lower_bound _ _ (radialDirection x) (radialDirection_norm x hn))

theorem smoothPhysicalSource_flux_lower_bound_ae (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    ∀ᵐ x ∂volume, 2 * p.radius + 2 ≤ ‖x‖ →
      -((magneticDecayConstant k / ‖x‖ * ∫ y : Position, ‖p.current y‖) *
        (radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖)) ≤
        (pairing (smoothElectricSource k p x)
          (cross (smoothMagneticSource k p x) (complexify (radialDirection x)))).re := by
  have hex : ∀ᵐ x ∂volume, x ∈ currentExterior p →
      exteriorElectric k p x = electricVolumeField k p x :=
    (ae_restrict_iff' (currentExterior p).isOpen.measurableSet).mp (electricExterior_eq_ae k p)
  filter_upwards [hex, smoothElectricSource_eq_ae k p hp, smoothMagneticSource_eq_ae k p hp]
    with x hx he hm
  intro hfar
  have hxf : p.radius + 1 ≤ ‖x‖ := by linarith [p.radius_nonneg]
  have hxs : x ∈ currentExterior p := by
    change p.radius + 1 < ‖x‖
    linarith [p.radius_nonneg]
  rw [he, hm, ← hx hxs, ← magneticExterior_eq_pointwise_far k p x hxf]
  exact exterior_poynting_flux_lower_bound k p x hfar

end OQ7Prescribed
