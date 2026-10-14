import work.BodySlabError

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace OQ7Prescribed
open Set MeasureTheory

def bodyCosMultiplier (B : TwoLayerBody) (θ : ℝ) : ScalarVolumeL2 →L[ℂ] ScalarVolumeL2 :=
  scalarPiecewiseL2 volume (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B) 1 (Real.cos θ)

def bodySinMultiplier (B : TwoLayerBody) (θ : ℝ) : ScalarVolumeL2 →L[ℂ] ScalarVolumeL2 :=
  scalarPiecewiseL2 volume (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B) 0 (Real.sin θ)

def bodyCompressFourErrors (B : TwoLayerBody) (θ : ℝ) (D00 D10 D01 D11 : ScalarVolumeL2) :
    ScalarBodyCurrentL2 B :=
  setRestrictionCLM volume B.domain (bodyDomain_isOpen B).measurableSet
    (bodyCosMultiplier B θ (D00 + D10) + bodySinMultiplier B θ (D01 + D11))

theorem bodyCompressFourErrors_norm_le (B : TwoLayerBody) (θ : ℝ) (D00 D10 D01 D11 : ScalarVolumeL2) :
    ‖bodyCompressFourErrors B θ D00 D10 D01 D11‖ ≤ ‖D00‖ + ‖D10‖ + (‖D01‖ + ‖D11‖) := by
  have hc := scalarPiecewiseL2_norm_le (volume : Measure Position) (bodyAbsorberSlice B)
    (bodyAbsorberSlice_measurable B) 1 (Real.cos θ) (by norm_num)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ) (D00 + D10)
  have hs := scalarPiecewiseL2_norm_le (volume : Measure Position) (bodyAbsorberSlice B)
    (bodyAbsorberSlice_measurable B) 0 (Real.sin θ) (by norm_num)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one θ) (D01 + D11)
  exact (indicatorL2_norm_le volume B.domain (bodyDomain_isOpen B).measurableSet _).trans
    ((norm_add_le _ _).trans ((add_le_add hc hs).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))))

theorem bodyCompressFourErrors_coe (B : TwoLayerBody) (θ : ℝ) (D00 D10 D01 D11 : ScalarVolumeL2) :
    (bodyCompressFourErrors B θ D00 D10 D01 D11 : ScalarVolumeL2) =ᵐ[volume]
      B.domain.indicator (fun x => if x 2 < B.absorberThickness then D00 x + D10 x
        else (Real.cos θ : ℂ) * (D00 x + D10 x) + (Real.sin θ : ℂ) * (D01 x + D11 x)) := by
  let C := bodyCosMultiplier B θ (D00 + D10)
  let S := bodySinMultiplier B θ (D01 + D11)
  filter_upwards [indicatorL2_coe volume B.domain (bodyDomain_isOpen B).measurableSet (C + S),
    Lp.coeFn_add C S, scalarPiecewiseL2_coe volume (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B) 1 (Real.cos θ) (D00 + D10),
    scalarPiecewiseL2_coe volume (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B) 0 (Real.sin θ) (D01 + D11),
    Lp.coeFn_add D00 D10, Lp.coeFn_add D01 D11] with x hi ha hc hs h0 h1
  change indicatorL2 volume B.domain (bodyDomain_isOpen B).measurableSet (C + S) x = _
  rw [hi]
  by_cases hx : x ∈ B.domain
  · rw [indicator_of_mem hx, indicator_of_mem hx, ha]
    change C x + S x = _
    change C x = _ at hc
    change S x = _ at hs
    rw [hc, hs]
    simp only [bodyAbsorberSlice, mem_setOf_eq]
    by_cases hz : x 2 < B.absorberThickness <;> simp only [hz, ite_true, ite_false]
    all_goals rw [h0, h1]
    all_goals simp only [Pi.add_apply, one_mul, zero_mul, add_zero]
  · simp only [indicator_of_notMem hx]

theorem bodyCompressedOutgoing_coe (k : ℝ) (B : TwoLayerBody) (θ : ℝ) (f : ScalarBodyCurrentL2 B) :
    (activeProjection B (basisR 0) (rotatedAxis θ)
      (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) f)) : ScalarVolumeL2) =ᵐ[volume]
        B.domain.indicator (fun x => if x 2 < B.absorberThickness then
          axisCoupling (basisR 0) (electricVolumeField k (bodyCurrentPolarization B
            (activeInjection B (basisR 0) (rotatedAxis θ) f)) x)
          else axisCoupling (rotatedAxis θ) (electricVolumeField k (bodyCurrentPolarization B
            (activeInjection B (basisR 0) (rotatedAxis θ) f)) x)) := by
  filter_upwards [activeProjection_coe B (basisR 0) (rotatedAxis θ)
    (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) f)),
    bodyOutgoingOperator_coe k B (activeInjection B (basisR 0) (rotatedAxis θ) f)] with x hp ht
  rw [hp, ht]
  by_cases hx : x ∈ B.domain
  · simp only [indicator_of_mem hx]
  · simp [indicator_of_notMem hx, axisCoupling]

theorem bodyCompressed_aperture_error_identity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (hR : 1 ≤ B.aperture)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (θ : ℝ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    activeProjection B (basisR 0) (rotatedAxis θ) (bodyOutgoingOperator k B
      (activeInjection B (basisR 0) (rotatedAxis θ) (bodyScaledScalarLift B w hw hwc hs q))) -
        bodyScaledScalarLift B w hw hwc hs
          (planarActiveOutgoing k hk _ (bodyHeight_pos B).le B.absorberThickness θ q) =
      bodyCompressFourErrors B θ
        (bodySlabError k hk B hR w hw hwc hs 1 1 (planarLayerAxisMap _ B.absorberThickness 1 (Real.cos θ) q))
        (bodySlabError k hk B hR w hw hwc hs Complex.I 1 (planarLayerAxisMap _ B.absorberThickness 0 (Real.sin θ) q))
        (bodySlabError k hk B hR w hw hwc hs 1 Complex.I (planarLayerAxisMap _ B.absorberThickness 1 (Real.cos θ) q))
        (bodySlabError k hk B hR w hw hwc hs Complex.I Complex.I (planarLayerAxisMap _ B.absorberThickness 0 (Real.sin θ) q)) := by
  let C := planarLayerAxisMap (B.absorberThickness + B.plateThickness) B.absorberThickness 1 (Real.cos θ) q
  let S := planarLayerAxisMap (B.absorberThickness + B.plateThickness) B.absorberThickness 0 (Real.sin θ) q
  let T := planarActiveOutgoing k hk _ (bodyHeight_pos B).le B.absorberThickness θ q
  let F := bodyScaledScalarLift B w hw hwc hs
  let V := activeProjection B (basisR 0) (rotatedAxis θ)
    (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) (F q)))
  let D (u v : ℂ) (f : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :=
    bodySlabError k hk B hR w hw hwc hs u v f
  have hi11 : inner ℝ (1 : ℂ) 1 = 1 := by simp [real_inner_eq_re_inner ℂ]
  have hiI1 : inner ℝ Complex.I (1 : ℂ) = 0 := by simp [real_inner_eq_re_inner ℂ]
  have hi1I : inner ℝ (1 : ℂ) Complex.I = 0 := by simp [real_inner_eq_re_inner ℂ]
  have hiII : inner ℝ Complex.I Complex.I = 1 := by simp [real_inner_eq_re_inner ℂ]
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (V : ScalarVolumeL2) (F T : ScalarVolumeL2),
    bodyCompressedOutgoing_coe k B θ (F q),
    bodySeparatedScalarLift_coe B _ _ _ T,
    slabHeight_quasiMeasurePreserving.ae (planarActiveOutgoing_coe k hk _ (bodyHeight_pos B).le B.absorberThickness θ q),
    bodyScaledLayerField_decomposition k B hR w hw hwc hs θ q,
    bodyCompressFourErrors_coe B θ (D 1 1 C) (D Complex.I 1 S) (D 1 Complex.I C) (D Complex.I Complex.I S),
    bodySlabError_coe k hk B hR w hw hwc hs 1 1 C,
    bodySlabError_coe k hk B hR w hw hwc hs Complex.I 1 S,
    bodySlabError_coe k hk B hR w hw hwc hs 1 Complex.I C,
    bodySlabError_coe k hk B hR w hw hwc hs Complex.I Complex.I S,
    (F T).property] with x hsub hv hF hT hfield herror h00 h10 h01 h11 houtside
  change ((V : ScalarVolumeL2) - (F T : ScalarVolumeL2)) x = _
  rw [hsub]
  change (V : ScalarVolumeL2) x - (F T : ScalarVolumeL2) x = _
  change (V : ScalarVolumeL2) x = _ at hv
  change (F T : ScalarVolumeL2) x = _ at hF
  change (F T : ScalarVolumeL2) x = scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (T : HeightL2) (x 2) at hF
  change (T : HeightL2) (x 2) = _ at hT
  change (bodyCompressFourErrors B θ (D 1 1 C) (D Complex.I 1 S) (D 1 Complex.I C) (D Complex.I Complex.I S) : ScalarVolumeL2) x = _ at herror
  rw [hv, hF, herror]
  change B.domain.indicator _ x - scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (T : HeightL2) (x 2) = _
  by_cases hx : x ∈ B.domain
  · have hobs := bodyDomain_subset_slabObservation B hx
    have hz : x 2 ∈ Icc 0 (B.absorberThickness + B.plateThickness) :=
      ⟨hx.2.1.le, hx.2.2.le⟩
    rw [indicator_of_mem hx, indicator_of_mem hx, hT, indicator_of_mem hz, hfield]
    change (D 1 1 C) x = _ at h00
    change (D Complex.I 1 S) x = _ at h10
    change (D 1 Complex.I C) x = _ at h01
    change (D Complex.I Complex.I S) x = _ at h11
    rw [h00, h10, h01, h11]
    simp only [indicator_of_mem hobs, hi11, hiI1, hi1I, hiII, mul_one, mul_zero,
      zero_smul, sub_zero, Complex.real_smul]
    dsimp only [C, S]
    by_cases ha : x 2 < B.absorberThickness <;> simp only [ha, ite_true, ite_false]
    · rw [axisCoupling_add, ← slabPosition_one]
      ring
    · rw [axisCoupling_add, axisCoupling_rotatedAxis, axisCoupling_rotatedAxis]
      ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    rw [← hF, houtside hx, sub_self]

end OQ7Prescribed
