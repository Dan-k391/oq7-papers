import PrescribedExtinction.PlanarSlabAbsorberPower
import PrescribedExtinction.PlanarRotationPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory Filter
open scoped Topology

def slabFormulaAsymmetry (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ)
    (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p) : ℝ :=
  |slabIntegralAbsorption k A W θ .plus hpA hpW - slabIntegralAbsorption k A W θ .minus hpA hpW| /
    slabFormulaExtinction k A W θ

theorem planarNormalizedAsymmetry_eq_slabFormula (k : ℝ) (hk : 0 < k)
    (A W : OQ7.HomogeneousLayer) (θ : ℝ) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 < A.q) (hqW : 0 < W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) :
    planarNormalizedAsymmetry k hk (A.width + W.width) (by linarith) A.width θ
      (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
      (by simpa only [relativePermittivity_susceptibility_im] using hqA)
      (by simpa only [relativePermittivity_susceptibility_im] using hqW) =
      slabFormulaAsymmetry k A W θ hpA hpW := by
  unfold planarNormalizedAsymmetry slabFormulaAsymmetry
  rw [planarNormalizedAbsorption_eq_slabIntegral k hk A W θ .plus hpA hpW hqA hqW hdA hdW,
    planarNormalizedAbsorption_eq_slabIntegral k hk A W θ .minus hpA hpW hqA hqW hdA hdW,
    planarNormalizedExtinction_plus_eq_slabFormula k hk A W θ hpA hpW hqA hqW hdA hdW]

theorem losslessPlateDesign_asymmetry_value (k : ℝ) (hk : 0 < k)
    (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width)
    (j : ℕ) (hj : 1 ≤ j) :
    slabFormulaAsymmetry k A (dielectricSlab (plateDesignPermittivity j) 0 (plateDesignThickness k j)) 0
      hpA (by dsimp [dielectricSlab]; linarith [plateDesignPermittivity_pos_susceptibility j hj]) =
      OQ7.absorptanceLeft (dielectricSlabReflection k A.p A.q A.width)
        (dielectricSlabTransmission k A.p A.q A.width) := by
  have hv := losslessPlateDesign_coupled_power_values k hk A hpA hqA hdA j hj
  have hA := (OQ7.passive_absorptances_nonneg
    (dielectricSlab_passive k hk A.p A.q A.width hpA hqA hdA)).1
  unfold slabFormulaAsymmetry
  rw [hv.1, hv.2.1, hv.2.2, zero_sub, abs_neg, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hA]
  ring

theorem slabDesignAsymmetry_joint_continuousAt_zero (k : ℝ) (hk : 0 < k)
    (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width)
    (j : ℕ) (hj : 1 ≤ j) :
    ContinuousAt (fun x : NonnegativeSlabLoss × ℝ =>
      slabFormulaAsymmetry k A (dielectricSlab (plateDesignPermittivity j) x.1 (plateDesignThickness k j)) x.2
        hpA (by dsimp [dielectricSlab]; linarith [plateDesignPermittivity_pos_susceptibility j hj]))
      ((⟨0, le_rfl⟩ : NonnegativeSlabLoss), 0) := by
  have hp : 1 ≤ plateDesignPermittivity j := by linarith [plateDesignPermittivity_pos_susceptibility j hj]
  have hd := (plateDesignThickness_pos k hk j hj).le
  have hB (σ : Direction) := slabIntegralAbsorption_loss_angle_continuous k hk A hpA hqA hdA
    (plateDesignPermittivity j) (plateDesignThickness k j) hp hd
    (fun x : NonnegativeSlabLoss × ℝ => x.1) (fun x => x.2) continuous_fst continuous_snd σ
  have hY := slabFormulaExtinction_loss_angle_continuous k hk A hpA hqA hdA
    (plateDesignPermittivity j) (plateDesignThickness k j) hp hd
    (fun x : NonnegativeSlabLoss × ℝ => x.1) (fun x => x.2) continuous_fst continuous_snd
  have hY0 := (losslessPlateDesign_coupled_power_values k hk A hpA hqA hdA j hj).2.2
  exact ((hB .plus).sub (hB .minus)).abs.continuousAt.div hY.continuousAt (by rw [hY0]; norm_num)

theorem exists_positive_loss_plate_design_asymmetry (k : ℝ) (hk : 0 < k)
    (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p) (hqA : 0 < A.q) (hdA : 0 < A.width)
    (j : ℕ) (hj : 1 ≤ j) (Q ε : ℝ) (hQ : 0 < Q)
    (hA : 1 - ε < OQ7.absorptanceLeft (dielectricSlabReflection k A.p A.q A.width)
      (dielectricSlabTransmission k A.p A.q A.width)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Q / 3 ∧
      1 - ε < slabFormulaAsymmetry k A
        (dielectricSlab (plateDesignPermittivity j) δ (plateDesignThickness k j)) 0
        hpA (by dsimp [dielectricSlab]; linarith [plateDesignPermittivity_pos_susceptibility j hj]) := by
  let f := fun q : NonnegativeSlabLoss => slabFormulaAsymmetry k A
    (dielectricSlab (plateDesignPermittivity j) q (plateDesignThickness k j)) 0
      hpA (by dsimp [dielectricSlab]; linarith [plateDesignPermittivity_pos_susceptibility j hj])
  have hf : ContinuousAt f (⟨0, le_rfl⟩ : NonnegativeSlabLoss) :=
    (slabDesignAsymmetry_joint_continuousAt_zero k hk A hpA hqA.le hdA.le j hj).comp
      (f := fun q : NonnegativeSlabLoss => (q, (0 : ℝ)))
      (continuous_id.prodMk continuous_const).continuousAt
  have he : ∀ᶠ q : NonnegativeSlabLoss in 𝓝 (⟨0, le_rfl⟩ : NonnegativeSlabLoss), 1 - ε < f q :=
    hf.eventually_const_lt (by
      dsimp only [f]
      rw [losslessPlateDesign_asymmetry_value k hk A hpA hqA.le hdA.le j hj]
      exact hA)
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp he
  let δ := min (r / 2) (Q / 6)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, ?_, ?_⟩
  · have h := min_le_right (r / 2) (Q / 6)
    linarith
  · have hdist : dist (⟨δ, hδ.le⟩ : NonnegativeSlabLoss) (⟨0, le_rfl⟩ : NonnegativeSlabLoss) < r := by
      change dist δ 0 < r
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ]
      have h := min_le_left (r / 2) (Q / 6)
      linarith
    have hresult := he hdist
    exact hresult

end OQ7Prescribed
