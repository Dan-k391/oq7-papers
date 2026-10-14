import work.PlanarSlabDesignLimit
import PrescribedExtinction.PlanarAbsorberDesign

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem exists_planar_design_near_unit_asymmetry (k : ℝ) (hk : 0 < k)
    (P Q ε : ℝ) (hP : 1 < P) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ (A W : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
      (hqA : 0 < A.q) (hqW : 0 < W.q) (hdA : 0 < A.width) (hdW : 0 < W.width),
      A.p ≤ P ∧ W.p ≤ P ∧ A.q < Q / 3 ∧ W.q < Q / 3 ∧
      1 - ε < planarNormalizedAsymmetry k hk (A.width + W.width) (by linarith) A.width 0
        (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
        (by simpa only [relativePermittivity_susceptibility_im] using hqA)
        (by simpa only [relativePermittivity_susceptibility_im] using hqW) := by
  obtain ⟨j, hj, hjP⟩ := exists_plateDesign_within_cap P hP
  obtain ⟨η, h, hη, hηQ, hh, hAx, _⟩ := exists_nearlyPerfect_absorber_with_loss_cap k hk Q ε hQ hε
  let A := dielectricSlab 1 η h
  have hpA : 1 ≤ A.p := le_rfl
  have hqA : 0 < A.q := hη
  have hdA : 0 < A.width := hh
  obtain ⟨δ, hδ, hδQ, hΓ⟩ := exists_positive_loss_plate_design_asymmetry k hk A hpA hqA hdA j hj Q ε hQ hAx
  let W := dielectricSlab (plateDesignPermittivity j) δ (plateDesignThickness k j)
  have hpW : 1 ≤ W.p := by dsimp [W, dielectricSlab]; linarith [plateDesignPermittivity_pos_susceptibility j hj]
  have hqW : 0 < W.q := hδ
  have hdW : 0 < W.width := plateDesignThickness_pos k hk j hj
  refine ⟨A, W, hpA, hpW, hqA, hqW, hdA, hdW, hP.le, hjP, hηQ, hδQ, ?_⟩
  rw [planarNormalizedAsymmetry_eq_slabFormula k hk A W 0 hpA hpW hqA hqW hdA.le hdW.le]
  exact hΓ

end OQ7Prescribed
