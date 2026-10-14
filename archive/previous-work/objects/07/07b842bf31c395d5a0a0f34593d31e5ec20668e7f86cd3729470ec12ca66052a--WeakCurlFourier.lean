import work.WeakCurlPlaneWave
import PrescribedExtinction.FourierL1L2

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory FourierTransform

def bilinearFunctional (v : Vector) : Vector →L[ℂ] ℂ := ∑ i : Fin 3,
  v i • (PiLp.proj 2 (fun _ : Fin 3 => ℂ) i : Vector →L[ℂ] ℂ)

theorem bilinearFunctional_apply (v w : Vector) : bilinearFunctional v w = bilinear w v := by
  simp [bilinearFunctional, bilinear, PiLp.proj_apply, mul_comm]

def crossLeftOperator (n : Position) : Vector →L[ℂ] Vector := tensorMap
  ![![0, -(n 2 : ℂ), (n 1 : ℂ)], ![(n 2 : ℂ), 0, -(n 0 : ℂ)], ![-(n 1 : ℂ), (n 0 : ℂ), 0]]

theorem crossLeftOperator_apply (n : Position) (v : Vector) :
    crossLeftOperator n v = cross (complexify n) v := by
  ext i
  fin_cases i <;> simp [crossLeftOperator, tensorMap_apply, tensorApply, Matrix.mulVec,
    dotProduct, cross, complexify, Fin.sum_univ_succ] <;> ring

theorem integrable_currentPlanePhase_smul (k : ℝ) (n : Position) (F : Field)
    (hF : Integrable F volume) : Integrable (fun x => currentPlanePhase k n x • F x) volume := by
  have hm : Measurable (currentPlanePhase k n) := (currentPlanePhase_contDiff k n).continuous.measurable
  apply hF.norm.mono' (hm.aestronglyMeasurable.smul hF.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by simp [norm_smul, currentPlanePhase_norm])

theorem weakCurl_compact_planeWave_transform (F G : Field)
    (hFI : Integrable F volume) (hGI : Integrable G volume) (hcurl : HasWeakCurl F G)
    (R : ℝ) (hR : 0 ≤ R)
    (hF : ∀ x, R < ‖x‖ → F x = 0) (hG : ∀ x, R < ‖x‖ → G x = 0)
    (k : ℝ) (n : Position) :
    (∫ x : Position, currentPlanePhase k n x • G x) =
      (Complex.I * (k : ℂ)) • crossLeftOperator n (∫ x : Position, currentPlanePhase k n x • F x) := by
  have hf := integrable_currentPlanePhase_smul k n F hFI
  have hg := integrable_currentPlanePhase_smul k n G hGI
  let a := Complex.I * (k : ℂ)
  have ht : Integrable (fun x => a • crossLeftOperator n (currentPlanePhase k n x • F x)) volume :=
    ((crossLeftOperator n).integrable_comp hf).smul a
  have hleft (v : Vector) :
      (∫ x : Position, bilinear (F x) ((-Complex.I * (k : ℂ) * currentPlanePhase k n x) • cross (complexify n) v)) =
        bilinearFunctional v (a • crossLeftOperator n (∫ x : Position, currentPlanePhase k n x • F x)) := by
    have heq (x : Position) :
        bilinear (F x) ((-Complex.I * (k : ℂ) * currentPlanePhase k n x) • cross (complexify n) v) =
          bilinearFunctional v (a • crossLeftOperator n (currentPlanePhase k n x • F x)) := by
      simp [bilinearFunctional_apply, crossLeftOperator_apply, a, bilinear, cross,
        complexify, PiLp.smul_apply, Fin.sum_univ_three]
      ring
    simp_rw [heq]
    rw [(bilinearFunctional v).integral_comp_comm ht, integral_smul,
      (crossLeftOperator n).integral_comp_comm hf]
  have hright (v : Vector) :
      (∫ x : Position, bilinear (G x) (currentPlanePhase k n x • v)) =
        bilinearFunctional v (∫ x : Position, currentPlanePhase k n x • G x) := by
    have heq (x : Position) : bilinear (G x) (currentPlanePhase k n x • v) =
        bilinearFunctional v (currentPlanePhase k n x • G x) := by
      simp [bilinearFunctional_apply, bilinear, PiLp.smul_apply, Finset.mul_sum, mul_left_comm, mul_assoc]
    simp_rw [heq]
    exact (bilinearFunctional v).integral_comp_comm hg
  ext j
  have h := weakCurl_compact_planeWave_pairing F G hcurl R hR hF hG k n (basisC j)
  rw [hleft, hright] at h
  simpa [bilinearFunctional_apply, bilinear, basisC, a] using h.symm

theorem physicalCurlSymbol_hermitian (k : ℝ) (n : Position) (u v : Vector) :
    inner ℂ u ((Complex.I * (k : ℂ)) • crossLeftOperator n v) =
      inner ℂ ((Complex.I * (k : ℂ)) • crossLeftOperator n u) v := by
  rw [← pairing_eq_inner, ← pairing_eq_inner]
  simp [crossLeftOperator_apply, pairing, cross, complexify, PiLp.smul_apply,
    Fin.sum_univ_three, map_add, map_sub, map_mul]
  ring

theorem fourier_eq_currentPlanePhase (F : Field) (ξ : Position) :
    𝓕 F ξ = ∫ x : Position, currentPlanePhase (2 * Real.pi) ξ x • F x := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) • F x =
    currentPlanePhase (2 * Real.pi) ξ x • F x
  congr 1
  unfold currentPlanePhase
  rw [realDot_eq_inner, real_inner_comm]
  congr 1
  push_cast
  ring

theorem weakCurl_compact_Fourier_symbol (F G : Field)
    (hFI : Integrable F volume) (hGI : Integrable G volume) (hcurl : HasWeakCurl F G)
    (R : ℝ) (hR : 0 ≤ R)
    (hF : ∀ x, R < ‖x‖ → F x = 0) (hG : ∀ x, R < ‖x‖ → G x = 0) (ξ : Position) :
    𝓕 G ξ = (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) • crossLeftOperator ξ (𝓕 F ξ) := by
  simp_rw [fourier_eq_currentPlanePhase]
  exact weakCurl_compact_planeWave_transform F G hFI hGI hcurl R hR hF hG (2 * Real.pi) ξ

/-- Integration by parts for nonsmooth compact weak-curl fields, proved
through the genuine Fourier integrals and the unitary L2 transform. -/
theorem compactWeakCurl_integral_inner (F G C D : Field)
    (hF1 : MemLp F 1 volume) (hF2 : MemLp F 2 volume)
    (hG1 : MemLp G 1 volume) (hG2 : MemLp G 2 volume)
    (hC1 : MemLp C 1 volume) (hC2 : MemLp C 2 volume)
    (hD1 : MemLp D 1 volume) (hD2 : MemLp D 2 volume)
    (hFC : HasWeakCurl F C) (hGD : HasWeakCurl G D)
    (R : ℝ) (hR : 0 ≤ R)
    (hFs : ∀ x, R < ‖x‖ → F x = 0) (hGs : ∀ x, R < ‖x‖ → G x = 0)
    (hCs : ∀ x, R < ‖x‖ → C x = 0) (hDs : ∀ x, R < ‖x‖ → D x = 0) :
    inner ℂ (hF2.toLp F) (hD2.toLp D) = inner ℂ (hC2.toLp C) (hG2.toLp G) := by
  rw [← (Lp.fourierTransformₗᵢ Position Vector).inner_map_map (hF2.toLp F) (hD2.toLp D),
    ← (Lp.fourierTransformₗᵢ Position Vector).inner_map_map (hC2.toLp C) (hG2.toLp G)]
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourierIntegral_L1L2_ae hF1 hF2, fourierIntegral_L1L2_ae hG1 hG2,
    fourierIntegral_L1L2_ae hC1 hC2, fourierIntegral_L1L2_ae hD1 hD2] with ξ hf hg hc hd
  rw [← hf, ← hg, ← hc, ← hd,
    weakCurl_compact_Fourier_symbol G D (memLp_one_iff_integrable.mp hG1) (memLp_one_iff_integrable.mp hD1) hGD R hR hGs hDs,
    weakCurl_compact_Fourier_symbol F C (memLp_one_iff_integrable.mp hF1) (memLp_one_iff_integrable.mp hC1) hFC R hR hFs hCs]
  exact physicalCurlSymbol_hermitian (2 * Real.pi) ξ (𝓕 F ξ) (𝓕 G ξ)

end OQ7Prescribed
