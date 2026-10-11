import PrescribedExtinction.PlanarDrive
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarNormalizedDrive_norm_sq (k : ℝ) (σ : Direction) (L h : ℝ)
    (hh : 0 ≤ h) (hL : h ≤ L) : ‖planarNormalizedDrive k σ L h‖ ^ 2 = L - h := by
  let g := planarNormalizedDrive k σ L h
  have he : (fun z : ℝ => ‖(g : HeightL2) z‖ ^ 2) =ᵐ[volume]
      (Icc h L).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [planarNormalizedDrive_coe k σ L h] with z hz
    rw [hz]
    by_cases hc : z ∈ Icc 0 L <;> by_cases hi : z < h
    · have hn : z ∉ Icc h L := by intro hm; linarith [hm.1]
      simp [hc, hi, hn]
    · have hm : z ∈ Icc h L := ⟨le_of_not_gt hi, hc.2⟩
      simp [hc, hi, hm, planarIncidentPhase_norm]
    · have hn : z ∉ Icc h L := by intro hm; exact hc ⟨hh.trans hm.1, hm.2⟩
      simp [hc, hi, hn]
    · have hn : z ∉ Icc h L := by intro hm; exact hc ⟨hh.trans hm.1, hm.2⟩
      simp [hc, hi, hn]
  have ht := integral_congr_ae he
  rw [memLp_two_integral_norm_sq _ (Lp.memLp (g : HeightL2)), Lp.toLp_coeFn,
    integral_indicator measurableSet_Icc, integral_const] at ht
  change ‖g‖ ^ 2 = ((volume.restrict (Icc h L)) univ).toReal • (1 : ℝ) at ht
  rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hL), smul_eq_mul, mul_one] at ht
  exact ht

theorem planarNormalizedDrive_norm (k : ℝ) (σ : Direction) (L h : ℝ)
    (hh : 0 ≤ h) (hL : h ≤ L) : ‖planarNormalizedDrive k σ L h‖ = Real.sqrt (L - h) := by
  have hs := planarNormalizedDrive_norm_sq k σ L h hh hL
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr hL), Real.sqrt_nonneg (L - h), norm_nonneg (planarNormalizedDrive k σ L h)]

end OQ7Prescribed

