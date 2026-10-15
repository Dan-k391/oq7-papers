import PrescribedExtinction.SlabPhysicalAperture

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Convolution

def scalarPlanarPotential (k : ℝ) (q : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ t : ℝ, planarScalarGreen k (z - t) * q t

theorem planarScalarGreen_continuous (k : ℝ) : Continuous (planarScalarGreen k) := by
  unfold planarScalarGreen
  exact continuous_const.mul ((apertureOscillation_continuous k).comp continuous_abs)

theorem scalarPlanarPotential_convolution (k : ℝ) (q : ℝ → ℂ) :
    scalarPlanarPotential k q = q ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] planarScalarGreen k := by
  funext z
  exact integral_congr_ae (ae_of_all _ fun t => mul_comm _ _)

theorem scalarPlanarPotential_contDiff (k : ℝ) (q : ℝ → ℂ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarPlanarPotential k q) := by
  rw [scalarPlanarPotential_convolution]
  exact hqc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hq
    (planarScalarGreen_continuous k).locallyIntegrable

theorem planarSlabTransverse_factorization (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (x u v : ℂ) (z : ℝ) : planarSlabTransverse k w q x z u v =
    (k ^ 2 * inner ℝ u v : ℝ) • (w x * scalarPlanarPotential k q z) := by
  unfold planarSlabTransverse scalarPlanarPotential
  rw [← integral_const_mul, ← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    simp only [Complex.real_smul]
    ring)

theorem planarSlabTransverse_continuous_product (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : Continuous w) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q)
    (u v : ℂ) : Continuous (fun y : ℂ × ℝ => planarSlabTransverse k w q y.1 y.2 u v) := by
  simp_rw [planarSlabTransverse_factorization]
  exact (continuous_const : Continuous (fun _ : ℂ × ℝ => (k ^ 2 * inner ℝ u v : ℝ))).smul
    ((hw.comp continuous_fst).mul ((scalarPlanarPotential_contDiff k q hq hqc).continuous.comp continuous_snd))

end OQ7Prescribed
