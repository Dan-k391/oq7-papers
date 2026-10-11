import PrescribedExtinction.StaticFourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! The actual Fourier integral agrees almost everywhere with Mathlib's
unitary L² Fourier transform on L¹ ∩ L². The argument uses actual Fourier
integral pairing and uniqueness of locally integrable distributions. It
applies to scalar and vector complex Hilbert-valued functions. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory FourierTransform
open scoped SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem fourierIntegral_L1L2_schwartz_pairing {f : Position → F}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (φ : SchwartzMap Position ℂ) :
    (∫ ξ : Position, φ ξ • (𝓕 f) ξ) =
      ∫ ξ : Position, φ ξ •
        (Lp.fourierTransformₗᵢ Position F (hf2.toLp f) : Position → F) ξ := by
  have ht := congrArg (fun T : TemperedDistribution Position F => T φ)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at ht
  have hc : (∫ x : Position, (𝓕 φ) x • (hf2.toLp f : Position → F) x) =
      ∫ x : Position, (𝓕 φ) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  rw [hc] at ht
  have hp := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.lsmul ℂ ℂ (E := F))
    (L := innerₗ Position) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner φ.integrable
    ((memLp_one_iff_integrable).mp hf1)
  have hp' : (∫ x : Position, (𝓕 φ) x • f x) =
      ∫ ξ : Position, φ ξ • (𝓕 f) ξ := by
    simpa [SchwartzMap.fourier_coe] using! hp
  rw [← hp']
  exact ht

theorem fourierIntegral_L1L2_ae {f : Position → F}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    𝓕 f =ᵐ[volume]
      (Lp.fourierTransformₗᵢ Position F (hf2.toLp f) : Position → F) := by
  have hcont : Continuous (𝓕 f) := by
    rw [← Real.fourierTransform_toLp hf1]
    exact (Real.Lp.fourierTransform (hf1.toLp f)).continuous
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (Lp.fourierTransformₗᵢ Position F (hf2.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hgc
  let φ : SchwartzMap Position ℂ :=
    (hgc.comp_left (show Complex.ofRealCLM (0 : ℝ) = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hp := fourierIntegral_L1L2_schwartz_pairing hf1 hf2 φ
  have hc (x : Position) : φ x = (g x : ℂ) := rfl
  calc
    _ = ∫ x : Position, φ x • (𝓕 f) x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change g x • (𝓕 f) x = φ x • (𝓕 f) x
        rw [hc]
        exact RCLike.real_smul_eq_coe_smul (K := ℂ) (g x) ((𝓕 f) x)
    _ = _ := hp
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change φ x • (Lp.fourierTransformₗᵢ Position F (hf2.toLp f) : Position → F) x =
          g x • (Lp.fourierTransformₗᵢ Position F (hf2.toLp f) : Position → F) x
        rw [hc]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (g x)
          ((Lp.fourierTransformₗᵢ Position F (hf2.toLp f) : Position → F) x)).symm

theorem fourierIntegral_L1L2_memLp {f : Position → F}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume := by
  exact (memLp_congr_ae (fourierIntegral_L1L2_ae hf1 hf2)).mpr
    (Lp.memLp (Lp.fourierTransformₗᵢ Position F (hf2.toLp f)))

end OQ7Prescribed
