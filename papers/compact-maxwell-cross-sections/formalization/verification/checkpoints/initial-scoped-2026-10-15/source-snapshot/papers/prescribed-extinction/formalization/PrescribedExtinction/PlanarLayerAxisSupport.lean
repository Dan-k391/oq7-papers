import PrescribedExtinction.PlanarSingleLayerCurrent
import PrescribedExtinction.PlanarLayerKernel

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarLayerAxisMap_first_current (k h L : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (F : PlanarLayerField k 0 h) (a b : ℝ) :
    planarLayerAxisMap L h a b (planarLayerL2Current k 0 h L le_rfl hh hL F) =
      (a : ℂ) • planarLayerL2Current k 0 h L le_rfl hh hL F := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [planarLayerAxisMap_coe L h a b (planarLayerL2Current k 0 h L le_rfl hh hL F),
    planarLayerL2Current_coe k 0 h L le_rfl hh hL F,
    Lp.coeFn_smul (a : ℂ) (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2),
    volume.ae_ne h] with z hmap hq hs hzh
  rw [hmap]
  change _ = ((a : ℂ) • (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2) : HeightL2) z
  rw [hs]
  change (if z < h then (a : ℂ) * (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2) z
    else (b : ℂ) * (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2) z) =
      (a : ℂ) * (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2) z
  rw [hq]
  by_cases hm : z ∈ Ioc 0 h
  · have hlt : z < h := lt_of_le_of_ne hm.2 hzh
    simp only [if_pos hlt]
  · simp only [indicator_of_notMem hm, mul_zero, ite_self]

theorem planarLayerAxisMap_second_current (k h L : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (F : PlanarLayerField k h L) (a b : ℝ) :
    planarLayerAxisMap L h a b (planarLayerL2Current k h L L hh hL le_rfl F) =
      (b : ℂ) • planarLayerL2Current k h L L hh hL le_rfl F := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [planarLayerAxisMap_coe L h a b (planarLayerL2Current k h L L hh hL le_rfl F),
    planarLayerL2Current_coe k h L L hh hL le_rfl F,
    Lp.coeFn_smul (b : ℂ) (planarLayerL2Current k h L L hh hL le_rfl F : HeightL2)] with z hmap hq hs
  rw [hmap]
  change _ = ((b : ℂ) • (planarLayerL2Current k h L L hh hL le_rfl F : HeightL2) : HeightL2) z
  rw [hs]
  change (if z < h then (a : ℂ) * (planarLayerL2Current k h L L hh hL le_rfl F : HeightL2) z
    else (b : ℂ) * (planarLayerL2Current k h L L hh hL le_rfl F : HeightL2) z) =
      (b : ℂ) * (planarLayerL2Current k h L L hh hL le_rfl F : HeightL2) z
  rw [hq]
  by_cases hm : z ∈ Ioc h L
  · have hlt : ¬ z < h := not_lt.mpr hm.1.le
    simp only [if_neg hlt]
  · simp only [indicator_of_notMem hm, mul_zero, ite_self]

end OQ7Prescribed
