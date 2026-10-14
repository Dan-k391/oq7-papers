import work.PlanarSlabStrictAbsorption
import work.PlanarSlabThickLimit
import work.PlanarDielectricIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Filter
open scoped Topology

theorem dielectricSlab_absorptance_thick_limit (k : ℝ) (hk : 0 < k) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun d : ℝ => OQ7.absorptanceLeft (dielectricSlabReflection k p q d)
        (dielectricSlabTransmission k p q d))
      atTop (𝓝 (1 - Complex.normSq (slabInterfaceReflection (dielectricSlabIndex p q)))) := by
  simpa only [dielectricSlabReflection, dielectricSlabTransmission, OQ7.layerTransfer,
    OQ7.refractiveIndex, OQ7.relativePermittivity, dielectricSlab, dielectricSlabIndex] using
    homogeneousSlabAbsorptance_thick_limit k hk (dielectricSlabIndex p q)
      (dielectricSlabIndex_ne_zero p q hp) (dielectricSlabIndex_one_add_ne_zero p q hp)
      (dielectricSlabIndex_im_pos p q hp hq)

theorem exists_nearlyPerfect_absorber_with_loss_cap (k : ℝ) (hk : 0 < k) (Q ε : ℝ)
    (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ η h : ℝ, 0 < η ∧ η < Q / 3 ∧ 0 < h ∧
      1 - ε < OQ7.absorptanceLeft (dielectricSlabReflection k 1 η h) (dielectricSlabTransmission k 1 η h) ∧
      OQ7.absorptanceLeft (dielectricSlabReflection k 1 η h) (dielectricSlabTransmission k 1 η h) < 1 := by
  obtain ⟨η, hη, hηQ, hρ⟩ := exists_weakDielectric_interface_with_loss_cap Q (ε / 2) hQ (by positivity)
  have hlim := dielectricSlab_absorptance_thick_limit k hk 1 η (by norm_num) hη
  have hb : 1 - ε < 1 - Complex.normSq (slabInterfaceReflection (dielectricSlabIndex 1 η)) := by linarith
  have he := hlim.eventually_const_lt hb
  obtain ⟨h, hpower, hpos⟩ := (he.and (eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨η, h, hη, hηQ, hpos, hpower,
    dielectricSlab_absorptance_lt_one k hk 1 η h le_rfl hη.le hpos.le⟩

end OQ7Prescribed
