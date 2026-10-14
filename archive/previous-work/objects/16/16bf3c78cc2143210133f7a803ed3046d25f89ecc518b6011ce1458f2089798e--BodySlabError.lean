import work.BodyScaledLift
import work.BodySlabGeometry
import work.ScalarPiecewiseL2
import PrescribedExtinction.PlanarLayerNorm

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def bodySlabError (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (hR : 1 ≤ B.aperture)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (u v : ℂ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) : ScalarVolumeL2 :=
  scaledSlabApertureDifference k hk w hw hwc 1 1 (B.absorberThickness + B.plateThickness)
    (by norm_num) (by norm_num) (bodyHeight_pos B).le
    (hs.trans horizontalSquareAperture_subset_ball) B.aperture hR u v
    (heightSupportEnlargement _ (planarHeightEmbedding _ (bodyHeight_pos B).le q))

theorem bodySlabError_coe (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (hR : 1 ≤ B.aperture)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (u v : ℂ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    bodySlabError k hk B hR w hw hwc hs u v q =ᵐ[volume]
      (slabObservationRegion B.aperture (B.absorberThickness + B.plateThickness + 2)).indicator (fun x =>
        axisCoupling (slabPosition v 0) (electricVolumeField k (bodySlabComponent B hR w hw hwc hs u q) x) -
          (k ^ 2 * inner ℝ u v : ℝ) • (scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) *
            scalarPlanarPotential k (q : HeightL2) (x 2))) := by
  have h := scaledSlabApertureDifference_coe k hk w hw hwc 1 1 _ (by norm_num) (by norm_num)
    (bodyHeight_pos B).le (hs.trans horizontalSquareAperture_subset_ball) B.aperture hR u v
    (planarHeightEmbedding _ (bodyHeight_pos B).le q)
  simp only [planarSlabTransverse_factorization, one_mul] at h
  convert h using 1
  all_goals rfl

theorem bodySlabError_uniform_bound (k : ℝ) (hk : 0 < k) (h d : ℝ) (hH : 0 ≤ h + d)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      ∀ (hR : 1 ≤ B.aperture) (u v : ℂ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
        ∀ q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness),
          ‖bodySlabError k hk B hR w hw hwc hs u v q‖ ≤ K * ‖q‖ := by
  obtain ⟨K, hK, he⟩ := physicalSlab_uniform_L2_aperture_residual k hk w hw hwc 1 1 (h + d)
    (by norm_num) (by norm_num) hH (hs.trans horizontalSquareAperture_subset_ball)
  refine ⟨K, hK, ?_⟩
  intro B hh hd hR u v hu hv q
  have hH' : B.absorberThickness + B.plateThickness = h + d := by rw [hh, hd]
  have hb := he B.aperture hR u v hu hv
  subst h
  subst d
  exact hb (planarHeightEmbedding _ (bodyHeight_pos B).le q)

end OQ7Prescribed
