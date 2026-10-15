import PrescribedExtinction.PhysicalCompactLossBracket
import PrescribedExtinction.IsotropicPhysicalStrictLoss

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set

theorem physicalIsotropic_prescribedExtinctionOfPlanarDesign (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (target m cap : ℝ) (htarget : 0 < target) (hcap : 0 < cap)
    (hm : m < planarNormalizedAsymmetry k hk (h + d) (by linarith) h 0 α β hα hβ) :
    ∃ (B : TwoLayerBody) (ν θ : ℝ), B.absorberThickness = h ∧ B.plateThickness = d ∧
      0 < ν ∧ ν < cap ∧ θ ∈ Ioo 0 Real.pi ∧
      IsUnit (physicalElectricOperator k B ν θ α β) ∧
      physicalPerturbedExtinction k B .plus ν θ α β = target ∧
      physicalPerturbedExtinction k B .minus ν θ α β = target ∧
      m < physicalPerturbedAsymmetry k B ν θ α β ∧
      physicalPerturbedAsymmetry k B ν θ α β < 1 := by
  obtain ⟨B, a, b, hBh, hBd, ha, hab, hbπ, hlo, hhi, hG⟩ :=
    physicalRankOne_exists_extinction_bracket k hk h d hh hd α β hα hβ target m htarget hm
  have hsin (θ : ℝ) (hθ : θ ∈ Icc a b) : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hθ.1) (hθ.2.trans_lt hbπ)
  have hX0 (θ : ℝ) (hθ : θ ∈ Icc a b) : 0 < physicalPerturbedExtinction k B .plus 0 θ α β := by
    rw [physicalPerturbedExtinction_zero_eq_original k hk B .plus θ α β hα hβ,
      rankOneRotationExtinction_factorization]
    exact mul_pos (sq_pos_of_pos (hsin θ hθ)) (normalizedExtinction_pos k hk B .plus θ α β hα hβ)
  have hG0 (θ : ℝ) (hθ : θ ∈ Icc a b) : m < physicalPerturbedAsymmetry k B 0 θ α β := by
    rw [physicalPerturbedAsymmetry_zero_eq_original k hk B θ α β hα hβ]
    unfold rankOnePhysicalElectric
    rw [physicalAsymmetry_normalized_factorization k hk B θ (ne_of_gt (hsin θ hθ)) α β hα hβ]
    exact hG θ hθ
  obtain ⟨ν, hν, hνcap, hlow, hhigh, hall⟩ :=
    physicalPerturbed_preserves_compact_bracket k hk B α β hα hβ a b target m cap hcap hX0 hG0
      (by rw [physicalPerturbedExtinction_zero_eq_original k hk B .plus a α β hα hβ]; exact hlo)
      (by rw [physicalPerturbedExtinction_zero_eq_original k hk B .plus b α β hα hβ]; exact hhi)
  have hc : ContinuousOn (fun θ : ℝ => physicalPerturbedExtinction k B .plus ν θ α β) (Icc a b) := by
    intro θ hθ
    exact ((physicalPerturbedExtinction_joint_continuousAt k B .plus α β (ν, θ) (hall θ hθ).1).comp
      (f := fun θ : ℝ => (ν, θ)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨θ, hθ, hX⟩ := intermediate_value_Icc hab.le hc ⟨hlow.le, hhigh.le⟩
  have hL := (hall θ hθ).1
  refine ⟨B, ν, θ, hBh, hBd, hν, hνcap, ⟨ha.trans_le hθ.1, hθ.2.trans_lt hbπ⟩,
    hL, hX, ?_, (hall θ hθ).2.2, ?_⟩
  · rw [← physicalPerturbedExtinction_reciprocity k hk B ν θ α β hL]
    exact hX
  · exact physicalPerturbedAsymmetry_lt_one k hk B ν θ hν α β hα.le hβ.le hL (hall θ hθ).2.1

end OQ7Prescribed
