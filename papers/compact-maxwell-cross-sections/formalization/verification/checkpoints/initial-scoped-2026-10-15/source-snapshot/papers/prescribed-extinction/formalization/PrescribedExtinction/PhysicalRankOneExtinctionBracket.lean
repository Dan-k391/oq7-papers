import PrescribedExtinction.UniformPhysicalAsymmetry
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set Filter
open scoped Topology

def rankOneRotationExtinction (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  extinction k (rankOneBody B (basisR 0) (rotatedAxis θ) α β) σ
    (rankOnePhysicalElectric k hk B σ θ α β hα hβ)

theorem rankOneRotationExtinction_factorization (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    rankOneRotationExtinction k hk B σ θ α β hα hβ =
      (Real.sin θ) ^ 2 * normalizedExtinction k hk B σ θ α β hα hβ :=
  physicalExtinction_sine_squared_factorization k hk B σ θ α β hα hβ

theorem rankOneRotationExtinction_continuous (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ => rankOneRotationExtinction k hk B σ θ α β hα hβ) := by
  simp_rw [rankOneRotationExtinction_factorization]
  exact (Real.continuous_sin.pow 2).mul (normalizedExtinction_continuous k hk B σ α β hα hβ)

theorem physicalRankOne_exists_extinction_bracket (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (target m : ℝ) (htarget : 0 < target)
    (hm : m < planarNormalizedAsymmetry k hk (h + d) (by linarith) h 0 α β hα hβ) :
    ∃ (B : TwoLayerBody) (a b : ℝ), B.absorberThickness = h ∧ B.plateThickness = d ∧
      0 < a ∧ a < b ∧ b < Real.pi ∧
      rankOneRotationExtinction k hk B .plus a α β hα hβ < target ∧
      target < rankOneRotationExtinction k hk B .plus b α β hα hβ ∧
      ∀ θ ∈ Icc a b, m < normalizedRotationAsymmetry k hk B θ α β hα hβ := by
  let G := fun θ => planarNormalizedAsymmetry k hk (h + d) (by linarith) h θ α β hα hβ
  let M := (m + G 0) / 2
  let e := (G 0 - m) / 4
  have hepos : 0 < e := by dsimp [e, G]; linarith
  have hGc : Continuous G := planarNormalizedAsymmetry_continuous k hk (h + d) (by linarith)
    h hh.le (by linarith) α β hα hβ
  have hg : ∀ᶠ θ : ℝ in 𝓝 0, M < G θ := hGc.continuousAt.eventually_const_lt (by dsimp [M]; linarith)
  obtain ⟨ρ, hρ, hg⟩ := Metric.eventually_nhds_iff.mp hg
  let b := min (ρ / 2) (Real.pi / 2)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hbπ : b < Real.pi := by have h := min_le_right (ρ / 2) (Real.pi / 2); linarith [Real.pi_pos]
  have hbρ : b < ρ := by have h := min_le_left (ρ / 2) (Real.pi / 2); linarith
  have hG (θ : ℝ) (hθ : θ ∈ Icc 0 b) : M < G θ := by
    apply hg
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact hθ.2.trans_lt hbρ
  obtain ⟨Rg, hRg, hge⟩ := physicalBody_normalized_asymmetry_uniform_aperture_localization k hk
    h d hh hd α β hα hβ (Icc 0 b) isCompact_Icc e hepos
  let Y := planarNormalizedExtinction k hk .plus (h + d) (by linarith) h b α β hα hβ
  have hY : 0 < Y := planarNormalizedExtinction_pos k hk .plus (h + d) (by linarith) h b hh.le
    (by linarith) α β hα hβ
  have hsin : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  let s := (Real.sin b) ^ 2
  have hs : 0 < s := sq_pos_of_pos hsin
  obtain ⟨Rp, hRp, hpe⟩ := physicalBody_normalized_powers_uniform_aperture_localization k hk
    h d hh hd α β hα hβ (Y / 2) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (max Rg (max Rp (2 * target / (s * Y))))
  let R : ℝ := n
  have hR0 : 1 ≤ R := hRg.trans ((le_max_left _ _).trans hn.le)
  have hR : 0 < R := by linarith
  let B : TwoLayerBody := ⟨R, h, d, 1, 1, hR, hh, hd⟩
  have hBRg : Rg ≤ B.aperture := (le_max_left _ _).trans hn.le
  have hBRp : Rp ≤ B.aperture := (le_max_left _ _).trans ((le_max_right _ _).trans hn.le)
  have hGbody (θ : ℝ) (hθ : θ ∈ Icc 0 b) : m < normalizedRotationAsymmetry k hk B θ α β hα hβ := by
    have hloc := hge B rfl rfl hBRg θ hθ
    change |normalizedRotationAsymmetry k hk B θ α β hα hβ - G θ| ≤ e at hloc
    have hlo := (abs_le.mp hloc).1
    have hp := hG θ hθ
    dsimp [M, e] at hp hlo
    linarith
  have hXp : target < rankOneRotationExtinction k hk B .plus b α β hα hβ := by
    have he := hpe B rfl rfl hBRp .plus b
    have hy : R ^ 2 * (Y / 2) ≤ normalizedExtinction k hk B .plus b α β hα hβ := by
      have hlo := (abs_le.mp ((le_add_of_nonneg_right (abs_nonneg _)).trans he)).1
      change -(Y / 2 * R ^ 2) ≤ normalizedExtinction k hk B .plus b α β hα hβ - R ^ 2 * Y at hlo
      linarith
    have hbig : 2 * target / (s * Y) < R := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hn)
    have hprod : 2 * target < R * (s * Y) := (div_lt_iff₀ (mul_pos hs hY)).mp hbig
    have hR2 : R ≤ R ^ 2 := by nlinarith
    have hmono := mul_le_mul_of_nonneg_left hR2 (mul_nonneg hs.le hY.le)
    rw [rankOneRotationExtinction_factorization]
    change target < s * normalizedExtinction k hk B .plus b α β hα hβ
    have hp := mul_le_mul_of_nonneg_left hy hs.le
    nlinarith
  have hX0 : rankOneRotationExtinction k hk B .plus 0 α β hα hβ = 0 := by
    rw [rankOneRotationExtinction_factorization]
    simp
  have hlow : ∀ᶠ θ : ℝ in 𝓝 0, rankOneRotationExtinction k hk B .plus θ α β hα hβ < target :=
    (rankOneRotationExtinction_continuous k hk B .plus α β hα hβ).continuousAt.eventually_lt_const
      (by change rankOneRotationExtinction k hk B .plus 0 α β hα hβ < target; rw [hX0]; exact htarget)
  obtain ⟨r, hr, hlow⟩ := Metric.eventually_nhds_iff.mp hlow
  let a := min (r / 2) (b / 2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hab : a < b := by have h := min_le_right (r / 2) (b / 2); linarith
  refine ⟨B, a, b, rfl, rfl, ha, hab, hbπ, ?_, hXp, ?_⟩
  · apply hlow
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos ha]
    have h := min_le_left (r / 2) (b / 2)
    linarith
  · intro θ hθ
    exact hGbody θ ⟨ha.le.trans hθ.1, hθ.2⟩

theorem physicalRankOne_prescribedExtinctionOfPlanarDesign (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (target m : ℝ) (htarget : 0 < target)
    (hm : m < planarNormalizedAsymmetry k hk (h + d) (by linarith) h 0 α β hα hβ) :
    ∃ (B : TwoLayerBody) (θ : ℝ), B.absorberThickness = h ∧ B.plateThickness = d ∧
      θ ∈ Ioo 0 Real.pi ∧
      rankOneRotationExtinction k hk B .plus θ α β hα hβ = target ∧
      rankOneRotationExtinction k hk B .minus θ α β hα hβ = target ∧
      m < normalizedAsymmetry k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
        (rankOnePhysicalElectric k hk B .plus θ α β hα hβ)
        (rankOnePhysicalElectric k hk B .minus θ α β hα hβ) ∧
      normalizedAsymmetry k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
        (rankOnePhysicalElectric k hk B .plus θ α β hα hβ)
        (rankOnePhysicalElectric k hk B .minus θ α β hα hβ) < 1 := by
  obtain ⟨B, a, b, hBh, hBd, ha, hab, hbπ, hlo, hhi, hΓ⟩ :=
    physicalRankOne_exists_extinction_bracket k hk h d hh hd α β hα hβ target m htarget hm
  obtain ⟨θ, hθ, hX⟩ := intermediate_value_Icc hab.le
    (rankOneRotationExtinction_continuous k hk B .plus α β hα hβ).continuousOn ⟨hlo.le, hhi.le⟩
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hθπ : θ < Real.pi := hθ.2.trans_lt hbπ
  have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
  have hphys : normalizedAsymmetry k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
      (rankOnePhysicalElectric k hk B .plus θ α β hα hβ)
      (rankOnePhysicalElectric k hk B .minus θ α β hα hβ) =
      normalizedRotationAsymmetry k hk B θ α β hα hβ :=
    physicalAsymmetry_normalized_factorization k hk B θ hs α β hα hβ
  refine ⟨B, θ, hBh, hBd, ⟨hθ0, hθπ⟩, hX, ?_, ?_, ?_⟩
  · rw [rankOneRotationExtinction_factorization, ← normalizedExtinction_reciprocity,
      ← rankOneRotationExtinction_factorization]
    exact hX
  · rw [hphys]
    exact hΓ θ hθ
  · rw [hphys]
    exact normalizedRotationAsymmetry_lt_one k hk B θ α β hα hβ

end OQ7Prescribed
