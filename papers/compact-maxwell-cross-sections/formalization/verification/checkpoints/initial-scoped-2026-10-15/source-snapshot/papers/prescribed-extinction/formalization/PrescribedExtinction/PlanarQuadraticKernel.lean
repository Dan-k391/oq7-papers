import PrescribedExtinction.PlanarHeightGreen
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped ComplexConjugate

def kernelQuadratic (b : ℝ × ℝ → ℂ) (q : ℝ → ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, b p * conj (q p.1) * q p.2

theorem kernelQuadratic_integrable (b : ℝ × ℝ → ℂ) (q : ℝ → ℂ)
    (hq : Integrable q volume) (hb : AEStronglyMeasurable b volume)
    (C : ℝ) (hC : ∀ᵐ p : ℝ × ℝ ∂volume, ‖b p‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => b p * conj (q p.1) * q p.2) volume := by
  have hqstar : Integrable (fun z => conj (q z)) volume := Complex.conjCLE.toContinuousLinearMap.integrable_comp hq
  have hp := (hqstar.mul_prod hq).bdd_mul (by simpa only [← Measure.volume_eq_prod] using hb)
    (c := C) (by simpa only [← Measure.volume_eq_prod] using hC)
  simpa only [Measure.volume_eq_prod, mul_assoc] using hp

theorem kernelQuadratic_real_symmetric (b : ℝ × ℝ → ℝ) (q : ℝ → ℂ)
    (hb : ∀ p, b p.swap = b p) :
    (kernelQuadratic (fun p => (b p : ℂ)) q).im = 0 := by
  have he : conj (kernelQuadratic (fun p => (b p : ℂ)) q) = kernelQuadratic (fun p => (b p : ℂ)) q := by
    unfold kernelQuadratic
    rw [← integral_conj, Measure.volume_eq_prod, ← integral_prod_swap]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by
      simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply, hb]
      change (b p : ℂ) * q p.2 * conj (q p.1) = (b p : ℂ) * conj (q p.1) * q p.2
      ring
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  linarith

end OQ7Prescribed
