import GeneralizedResearch.PhysicalFourier
import PrescribedExtinction.FourierL1L2

/-! The unitary physical inverse transform agrees with its literal exp(i κ·x)
Bochner integral for every L¹ ∩ L² spectrum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.PhysicalFourier
open MeasureTheory FourierTransform
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem inverseIntegral_pairing {f : Transverse → E}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) (φ : SchwartzMap Transverse ℂ) :
    (∫ ξ : Transverse, φ ξ • (𝓕⁻ f) ξ) =
      ∫ ξ : Transverse, φ ξ • (BeamPackets.spatial (hf2.toLp f)) ξ := by
  have ht := congrArg (fun T : TemperedDistribution Transverse E => T φ)
    (Lp.fourierInv_toTemperedDistribution_eq (hf2.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at ht
  have hc : (∫ x : Transverse, (𝓕⁻ φ) x • (hf2.toLp f : Transverse → E) x) =
      ∫ x : Transverse, (𝓕⁻ φ) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  rw [hc] at ht
  have hp := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.lsmul ℂ ℂ (E := E))
    (L := -(innerₗ Transverse)) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner.neg φ.integrable
    ((memLp_one_iff_integrable).mp hf1)
  have hp' : (∫ x : Transverse, (𝓕⁻ φ) x • f x) =
      ∫ ξ : Transverse, φ ξ • (𝓕⁻ f) ξ := by
    have hflip : (-innerₗ Transverse).flip = -innerₗ Transverse := by
      ext x y
      simp [real_inner_comm]
    rw [hflip] at hp
    change (∫ x : Transverse, (𝓕⁻ (φ : Transverse → ℂ)) x • f x) =
      ∫ ξ : Transverse, φ ξ • (𝓕⁻ f) ξ at hp
    simpa only [SchwartzMap.fourierInv_coe] using hp
  rw [← hp']
  exact ht

theorem inverseIntegral_ae {f : Transverse → E}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    𝓕⁻ f =ᵐ[volume] (BeamPackets.spatial (hf2.toLp f) : Transverse → E) := by
  have hcont : Continuous (𝓕⁻ f) := by
    rw [← Real.Lp.fourierTransformInv_toLp hf1]
    exact (Real.Lp.fourierTransformInv (hf1.toLp f)).continuous
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (BeamPackets.spatial (hf2.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hgc
  let φ : SchwartzMap Transverse ℂ :=
    (hgc.comp_left (show Complex.ofRealCLM (0 : ℝ) = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hp := inverseIntegral_pairing hf1 hf2 φ
  have hc (x : Transverse) : φ x = (g x : ℂ) := rfl
  calc
    _ = ∫ x : Transverse, φ x • (𝓕⁻ f) x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change g x • (𝓕⁻ f) x = φ x • (𝓕⁻ f) x
        rw [hc]
        exact RCLike.real_smul_eq_coe_smul (K := ℂ) (g x) ((𝓕⁻ f) x)
    _ = _ := hp
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change φ x • (BeamPackets.spatial (hf2.toLp f)) x =
          g x • (BeamPackets.spatial (hf2.toLp f)) x
        rw [hc]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (g x)
          ((BeamPackets.spatial (hf2.toLp f)) x)).symm

def integralInverse (f : Transverse → E) (x : Transverse) : E :=
  (factor : ℂ) • ∫ q : Transverse, Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) • f q

omit [CompleteSpace E] in
theorem scaled_inverseIntegral (f : Transverse → E) (x : Transverse) :
    (factor : ℂ) • (𝓕⁻ f) (factor • x) = integralInverse f x := by
  rw [Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun q => by
    change Complex.exp (((2 * Real.pi * inner ℝ q (factor • x) : ℝ) : ℂ) * Complex.I) • f q =
      Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) • f q
    apply congrArg (fun z : ℂ => z • f q)
    apply congrArg Complex.exp
    rw [real_inner_smul_right]
    unfold factor
    push_cast
    field_simp)

theorem inverse_integral_ae {f : Transverse → E}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    (inverse (hf2.toLp f) : Transverse → E) =ᵐ[volume] integralInverse f := by
  have hs := (Measure.quasiMeasurePreserving_smul volume factor_pos.ne').ae
    (inverseIntegral_ae hf1 hf2)
  filter_upwards [inverse_ae (hf2.toLp f), hs] with x hx hsx
  rw [hx, ← hsx, scaled_inverseIntegral]

end GeneralizedResearch.PhysicalFourier
