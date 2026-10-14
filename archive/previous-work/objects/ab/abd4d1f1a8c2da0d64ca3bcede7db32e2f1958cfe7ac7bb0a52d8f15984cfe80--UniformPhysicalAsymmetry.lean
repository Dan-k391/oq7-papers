import work.PlanarRotationPowers
import work.PowerRatioEstimate
import PrescribedExtinction.UniformPhysicalPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set

theorem normalizedRotationAsymmetry_scaled (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedRotationAsymmetry k hk B θ α β hα hβ =
      |normalizedAbsorption k hk B .plus θ α β hα hβ / B.aperture ^ 2 -
        normalizedAbsorption k hk B .minus θ α β hα hβ / B.aperture ^ 2| /
      (normalizedExtinction k hk B .plus θ α β hα hβ / B.aperture ^ 2) := by
  unfold normalizedRotationAsymmetry
  rw [div_sub_div_same, abs_div, abs_of_pos (sq_pos_of_pos B.aperture_pos)]
  rw [div_div_div_cancel_right₀ (pow_ne_zero 2 B.aperture_pos.ne')]

theorem physicalBody_normalized_asymmetry_uniform_aperture_localization (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (s : Set ℝ) (hs : IsCompact s) (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      R0 ≤ B.aperture → ∀ θ ∈ s,
        |normalizedRotationAsymmetry k hk B θ α β hα hβ -
          planarNormalizedAsymmetry k hk (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ| ≤ ε := by
  obtain ⟨c, hc, hcb⟩ := planarNormalizedExtinction_compact_lower_bound k hk .plus (h + d)
    (by linarith) h hh.le (by linarith) α β hα hβ s hs
  let e := min (c / 2) (ε * c / 6)
  have hep : 0 < e := lt_min (by positivity) (by positivity)
  obtain ⟨R0, hR0, he⟩ := physicalBody_normalized_powers_uniform_aperture_localization k hk h d hh hd
    α β hα hβ e hep
  refine ⟨R0, hR0, ?_⟩
  intro B hBh hBd hBR θ hθ
  rcases B with ⟨R, bh, bd, aperm, wperm, hR, hbh, hbd⟩
  dsimp only at hBh hBd
  subst bh
  subst bd
  let B : TwoLayerBody := ⟨R, h, d, aperm, wperm, hR, hbh, hbd⟩
  let t := R ^ 2
  have ht : 0 < t := sq_pos_of_pos hR
  let x := normalizedExtinction k hk B .plus θ α β hα hβ
  let a := normalizedAbsorption k hk B .plus θ α β hα hβ
  let b := normalizedAbsorption k hk B .minus θ α β hα hβ
  let X := planarNormalizedExtinction k hk .plus (h + d) (by linarith) h θ α β hα hβ
  let A := planarNormalizedAbsorption k hk .plus (h + d) (by linarith) h θ α β hα hβ
  let C := planarNormalizedAbsorption k hk .minus (h + d) (by linarith) h θ α β hα hβ
  have hp := he B rfl rfl hBR .plus θ
  have hm := he B rfl rfl hBR .minus θ
  have hx : |x / t - X| ≤ e := scaledPower_error_bound x X t e ht
    ((le_add_of_nonneg_right (abs_nonneg _)).trans hp)
  have ha : |a / t - A| ≤ e := scaledPower_error_bound a A t e ht
    ((le_add_of_nonneg_left (abs_nonneg _)).trans hp)
  have hb : |b / t - C| ≤ e := scaledPower_error_bound b C t e ht
    ((le_add_of_nonneg_left (abs_nonneg _)).trans hm)
  have hX : c ≤ X := hcb θ hθ
  have hy : c / 2 ≤ x / t := by
    have hxe := (abs_le.mp hx).1
    have hec : e ≤ c / 2 := min_le_left _ _
    linarith
  have hAp : 0 < A := planarNormalizedAbsorption_pos k hk .plus (h + d) (by linarith) h θ
    hh.le (by linarith) α β hα hβ
  have hCp : 0 < C := planarNormalizedAbsorption_pos k hk .minus (h + d) (by linarith) h θ
    hh.le (by linarith) α β hα hβ
  have hAX : A ≤ X := planarNormalizedAbsorption_le_extinction k hk .plus (h + d) (by linarith) h θ α β hα hβ
  have hCX : C ≤ X := by
    have ht := planarNormalizedAbsorption_le_extinction k hk .minus (h + d) (by linarith) h θ α β hα hβ
    rw [← planarNormalizedExtinction_reciprocity k hk h d hh hd θ α β hα hβ] at ht
    exact ht
  have hN : |A - C| ≤ X := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : abs (abs (a / t - b / t) - abs (A - C)) ≤ 2 * e := by
    apply (abs_abs_sub_abs_le_abs_sub _ _).trans
    have hi : (a / t - b / t) - (A - C) = (a / t - A) - (b / t - C) := by ring
    rw [hi]
    exact (abs_sub _ _).trans (by linarith)
  have hratio := normalizedPowerRatio_error_bound |a / t - b / t| |A - C| (x / t) X c e
    hc hep.le hy hX (abs_nonneg _) hN hn hx
  have heε : 6 * e / c ≤ ε := by
    apply (div_le_iff₀ hc).mpr
    have hec : e ≤ ε * c / 6 := min_le_right _ _
    linarith
  change |normalizedRotationAsymmetry k hk B θ α β hα hβ -
    planarNormalizedAsymmetry k hk (h + d) (bodyHeight_pos B).le h θ α β hα hβ| ≤ ε
  rw [normalizedRotationAsymmetry_scaled]
  exact hratio.trans heε

theorem physicalRankOne_original_asymmetry_uniform_aperture_localization (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (s : Set ℝ) (hs : IsCompact s) (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      R0 ≤ B.aperture → ∀ θ ∈ s, Real.sin θ ≠ 0 →
        |normalizedAsymmetry k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
            (rankOnePhysicalElectric k hk B .plus θ α β hα hβ)
            (rankOnePhysicalElectric k hk B .minus θ α β hα hβ) -
          planarNormalizedAsymmetry k hk (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ| ≤ ε := by
  obtain ⟨R0, hR0, he⟩ := physicalBody_normalized_asymmetry_uniform_aperture_localization k hk h d hh hd
    α β hα hβ s hs ε hε
  refine ⟨R0, hR0, ?_⟩
  intro B hBh hBd hBR θ hθ hsine
  unfold rankOnePhysicalElectric
  rw [physicalAsymmetry_normalized_factorization k hk B θ hsine α β hα hβ]
  exact he B hBh hBd hBR θ hθ

end OQ7Prescribed
