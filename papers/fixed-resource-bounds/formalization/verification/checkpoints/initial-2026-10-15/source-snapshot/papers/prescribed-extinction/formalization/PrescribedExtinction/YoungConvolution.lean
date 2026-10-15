import PrescribedExtinction.RemainderCurrentPairing
import Mathlib.MeasureTheory.Function.L2Space

/-! An L¹-kernel / L²-current convolution bound. Unlike the earlier
pointwise L²/L² estimate, this permits the locally L¹ first Green derivative.
All actual convolution integrals exist almost everywhere; no value of an
undefined Bochner integral is used to supply a field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
open scoped Convolution

theorem weighted_integral_cauchy_sq (w g : Position → ℝ)
    (hw : Integrable w volume)
    (hwg : Integrable (fun y => w y * g y) volume)
    (hwg2 : Integrable (fun y => w y * g y ^ 2) volume)
    (hw0 : ∀ᵐ y ∂volume, 0 ≤ w y) :
    (∫ y : Position, w y * g y) ^ 2 ≤
      (∫ y : Position, w y) * (∫ y : Position, w y * g y ^ 2) := by
  let A := ∫ y : Position, w y
  let F := ∫ y : Position, w y * g y
  let B := ∫ y : Position, w y * g y ^ 2
  have hA : 0 ≤ A := integral_nonneg_of_ae hw0
  by_cases hz : A = 0
  · have hwz : w =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg_ae hw0 hw).mp hz
    have hF : F = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hwz] with y hy
      simp [hy]
    change F ^ 2 ≤ A * B
    simp [hz, hF]
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let t := F / A
    have hquad : 0 ≤ B - (2 * t) * F + t ^ 2 * A := by
      have hi := (hwg2.sub (hwg.const_mul (2 * t))).add (hw.const_mul (t ^ 2))
      have hn : 0 ≤ ∫ y : Position, w y * g y ^ 2 -
          (2 * t) * (w y * g y) + t ^ 2 * w y := by
        apply integral_nonneg_of_ae
        filter_upwards [hw0] with y hy
        have he : w y * g y ^ 2 - (2 * t) * (w y * g y) + t ^ 2 * w y =
            w y * (g y - t) ^ 2 := by ring
        rw [he]
        exact mul_nonneg hy (sq_nonneg _)
      have hs := integral_add (hwg2.sub (hwg.const_mul (2 * t))) (hw.const_mul (t ^ 2))
      have ht := integral_sub hwg2 (hwg.const_mul (2 * t))
      simp only [Pi.sub_apply] at hs ht
      rw [hs, ht, integral_const_mul, integral_const_mul] at hn
      exact hn
    have he : A * (B - (2 * t) * F + t ^ 2 * A) = A * B - F ^ 2 := by
      dsimp [t]
      field_simp
      ring
    have hn := mul_nonneg hA hquad
    rw [he] at hn
    change F ^ 2 ≤ A * B
    linarith

def scalarVectorConvolution (K : Position → ℂ) (f : Field) : Field :=
  fun x => ∫ y : Position, K y • f (x - y)

theorem scalarVectorConvolution_ae_integrable (K : Position → ℂ) (f : Field)
    (hK : Integrable K volume) (hf : Integrable f volume) :
    ∀ᵐ x ∂volume, Integrable (fun y : Position => K y • f (x - y)) volume :=
  hK.ae_convolution_exists vectorScalarMul.flip hf

theorem scalarVectorConvolution_memLp_two (K : Position → ℂ) (f : Field)
    (hK : Integrable K volume) (hf : Integrable f volume) (hf2 : MemLp f 2 volume) :
    MemLp (scalarVectorConvolution K f) 2 volume ∧
      (∫ x : Position, ‖scalarVectorConvolution K f x‖ ^ 2) ≤
        (∫ y : Position, ‖K y‖) ^ 2 * (∫ x : Position, ‖f x‖ ^ 2) := by
  have hfq : Integrable (fun x : Position => ‖f x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).mp hf2
  have hj := hK.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hfq
  have hq := hj.integral_prod_left
  have ha := hK.norm.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hf.norm
  have hc := scalarVectorConvolution_ae_integrable K f hK hf
  have hm : AEStronglyMeasurable (scalarVectorConvolution K f) volume :=
    hK.aestronglyMeasurable.convolution vectorScalarMul.flip hf.aestronglyMeasurable
  let A := ∫ y : Position, ‖K y‖
  let B := fun x : Position => ∫ y : Position, ‖K y‖ * ‖f (x - y)‖ ^ 2
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  have hB : ∀ x : Position, 0 ≤ B x := fun x => integral_nonneg (fun y => by positivity)
  have hb : ∀ᵐ x ∂volume, ‖scalarVectorConvolution K f x‖ ^ 2 ≤ A * B x := by
    filter_upwards [hj.prod_right_ae, ha, hc] with x hx hax hcx
    have hcs := weighted_integral_cauchy_sq (fun y => ‖K y‖)
      (fun y => ‖f (x - y)‖) hK.norm hax hx (ae_of_all _ fun y => norm_nonneg _)
    have hn : ‖scalarVectorConvolution K f x‖ ≤ ∫ y : Position, ‖K y‖ * ‖f (x - y)‖ := by
      simpa only [scalarVectorConvolution, norm_smul] using
        norm_integral_le_integral_norm (fun y : Position => K y • f (x - y))
    have hn0 : 0 ≤ ∫ y : Position, ‖K y‖ * ‖f (x - y)‖ :=
      integral_nonneg (fun y => by positivity)
    change ‖scalarVectorConvolution K f x‖ ^ 2 ≤ A * B x
    exact (sq_le_sq₀ (norm_nonneg _) hn0).mpr hn |>.trans hcs
  have hsq : Integrable (fun x : Position => ‖scalarVectorConvolution K f x‖ ^ 2) volume := by
    apply (hq.const_mul A).mono' (hm.norm.pow 2)
    filter_upwards [hb] with x hx
    simpa only [Pi.pow_apply, ContinuousLinearMap.mul_apply', Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (mul_nonneg hA (hB x))] using hx
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hsq, ?_⟩
  calc
    _ ≤ ∫ x : Position, A * B x := integral_mono_ae hsq (hq.const_mul A) hb
    _ = A * (∫ x : Position, B x) := integral_const_mul _ _
    _ = A * (A * ∫ x : Position, ‖f x‖ ^ 2) := by
      congr 1
      rw [show (∫ x : Position, B x) =
        ∫ y : Position, ∫ x : Position, ‖K y‖ * ‖f (x - y)‖ ^ 2 from integral_integral_swap hj]
      have ht (y : Position) : (∫ x : Position, ‖f (x - y)‖ ^ 2) =
          ∫ x : Position, ‖f x‖ ^ 2 :=
        integral_sub_right_eq_self (fun x : Position => ‖f x‖ ^ 2) y
      simp_rw [integral_const_mul, ht]
      rw [integral_mul_const]
    _ = _ := by dsimp [A]; ring

end OQ7Prescribed
