import work.PlanarCurrentSpace
import work.PlanarGreenWork

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory
open scoped ComplexConjugate

theorem planarScalarOutgoing_work (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L)
    (q : PlanarCurrentL2 L) :
    inner ℂ q (planarScalarOutgoing k hk L hL q) =
      kernelQuadratic (fun p => (k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) (q : HeightL2) := by
  have hq : Integrable (q : HeightL2) volume := heightSupportedProfile_integrable L (planarHeightEmbedding L hL q)
  have hb : AEStronglyMeasurable (fun p : ℝ × ℝ => (k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) volume :=
    (((planarScalarGreen_continuous k).comp (continuous_fst.sub continuous_snd)).const_smul (k ^ 2 : ℝ)).aestronglyMeasurable
  have hp := kernelQuadratic_integrable _ (q : HeightL2) hq hb (k ^ 2 * (1 / (2 * k)))
    (ae_of_all _ fun p => by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg k), planarScalarGreen_norm k _ hk])
  have hp' : Integrable (fun p : ℝ × ℝ => ((k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) *
      conj ((q : HeightL2) p.1) * (q : HeightL2) p.2) ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hp
  calc
    _ = ∫ z : ℝ, conj ((q : HeightL2) z) * ((k ^ 2 : ℝ) • scalarPlanarPotential k (q : HeightL2) z) := by
      change inner ℂ (q : HeightL2) (planarScalarOutgoing k hk L hL q : HeightL2) = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [planarScalarOutgoing_coe k hk L hL q, q.property] with z ht hz
      rw [ht]
      by_cases hm : z ∈ Icc 0 L
      · simp only [indicator_of_mem hm, RCLike.inner_apply, mul_comm]
      · simp only [indicator_of_notMem hm, hz hm, map_zero, zero_mul, mul_zero, inner_zero_left]
    _ = ∫ z : ℝ, ∫ t : ℝ, ((k ^ 2 : ℝ) • planarScalarGreen k (z - t)) *
        conj ((q : HeightL2) z) * (q : HeightL2) t := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        unfold scalarPlanarPotential
        change conj ((q : HeightL2) z) * ((k ^ 2 : ℝ) • ∫ t : ℝ, planarScalarGreen k (z - t) * (q : HeightL2) t) = _
        rw [Complex.real_smul, ← integral_const_mul, ← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun t => by simp only [Complex.real_smul]; ring
    _ = _ := by
      unfold kernelQuadratic
      rw [Measure.volume_eq_prod, integral_prod _ hp']

theorem planarScalarOutgoing_im_nonneg (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L)
    (q : PlanarCurrentL2 L) : 0 ≤ (inner ℂ q (planarScalarOutgoing k hk L hL q)).im := by
  rw [planarScalarOutgoing_work]
  exact kernelQuadratic_planar_im_nonneg k hk (q : HeightL2)
    (heightSupportedProfile_integrable L (planarHeightEmbedding L hL q))

end OQ7Prescribed
