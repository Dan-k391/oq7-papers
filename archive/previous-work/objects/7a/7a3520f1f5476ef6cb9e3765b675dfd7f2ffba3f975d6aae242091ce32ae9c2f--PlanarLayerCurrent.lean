import work.PlanarTwoLayerGreen
import PrescribedExtinction.PlanarCurrentSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Classical

theorem continuousOn_Ioc_indicator_memLp (a b : ℝ) (q : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b)) : MemLp ((Ioc a b).indicator q) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  apply MemLp.of_bound ((hq.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hC t (Ioc_subset_Icc_self ht)

theorem planarTwoLayerCurrent_memLp (h L : ℝ) (qA qW : ℝ → ℂ)
    (hA : ContinuousOn qA (Icc 0 h)) (hW : ContinuousOn qW (Icc h L)) :
    MemLp (planarTwoLayerCurrent h L qA qW) 2 volume :=
  (continuousOn_Ioc_indicator_memLp 0 h qA hA).add
    (continuousOn_Ioc_indicator_memLp h L qW hW)

def planarTwoLayerL2Current (k h L : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L) : PlanarCurrentL2 L :=
  ⟨(planarTwoLayerCurrent_memLp h L A.current W.current A.current_continuous W.current_continuous).toLp
    (planarTwoLayerCurrent h L A.current W.current), by
    filter_upwards [(planarTwoLayerCurrent_memLp h L A.current W.current
      A.current_continuous W.current_continuous).coeFn_toLp] with t ht
    intro hn
    rw [ht]
    have hA : t ∉ Ioc 0 h := fun hmem => hn ⟨hmem.1.le, hmem.2.trans hL⟩
    have hW : t ∉ Ioc h L := fun hmem => hn ⟨hh.trans hmem.1.le, hmem.2⟩
    simp only [planarTwoLayerCurrent, indicator_of_notMem hA, indicator_of_notMem hW, add_zero]⟩

theorem planarTwoLayerL2Current_coe (k h L : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L) :
    (planarTwoLayerL2Current k h L hh hL A W : HeightL2) =ᵐ[volume]
      planarTwoLayerCurrent h L A.current W.current :=
  (planarTwoLayerCurrent_memLp h L A.current W.current A.current_continuous W.current_continuous).coeFn_toLp

theorem scalarPlanarPotential_twoLayer_representation (k h L z : ℝ) (hk : k ≠ 0)
    (hh : 0 ≤ h) (hL : h ≤ L) (hz : z ∈ Icc 0 L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L)
    (hE : A.electric h = W.electric h) (hH : A.magnetic h = W.magnetic h) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k (planarTwoLayerL2Current k h L hh hL A W : HeightL2) z =
      (if z ≤ h then A.electric z else W.electric z) -
        (1 / 2 : ℂ) * apertureOscillation k z * (A.magnetic 0 + A.electric 0) +
        (1 / 2 : ℂ) * apertureOscillation k (L - z) * (W.magnetic L - W.electric L) := by
  have hi : scalarPlanarPotential k (planarTwoLayerL2Current k h L hh hL A W : HeightL2) z =
      ∫ t : ℝ, planarScalarGreen k (z - t) * planarTwoLayerCurrent h L A.current W.current t := by
    apply integral_congr_ae
    filter_upwards [planarTwoLayerL2Current_coe k h L hh hL A W] with t ht
    rw [ht]
  rw [hi, Complex.real_smul, Complex.ofReal_pow]
  exact planarTwoLayerGreen_interior_representation k h L z hk hh hL hz A W hE hH

theorem planarScalarOutgoing_twoLayer_representation (k : ℝ) (hk : 0 < k) (h L : ℝ)
    (hh : 0 ≤ h) (hL : h ≤ L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L)
    (hE : A.electric h = W.electric h) (hH : A.magnetic h = W.magnetic h) :
    (planarScalarOutgoing k hk L (hh.trans hL) (planarTwoLayerL2Current k h L hh hL A W) : HeightL2) =ᵐ[volume]
      (Icc 0 L).indicator (fun z =>
        (if z ≤ h then A.electric z else W.electric z) -
          (1 / 2 : ℂ) * apertureOscillation k z * (A.magnetic 0 + A.electric 0) +
          (1 / 2 : ℂ) * apertureOscillation k (L - z) * (W.magnetic L - W.electric L)) := by
  filter_upwards [planarScalarOutgoing_coe k hk L (hh.trans hL) (planarTwoLayerL2Current k h L hh hL A W)] with z hz
  rw [hz]
  by_cases hm : z ∈ Icc 0 L
  · simp only [indicator_of_mem hm]
    exact scalarPlanarPotential_twoLayer_representation k h L z hk.ne' hh hL hm A W hE hH
  · simp only [indicator_of_notMem hm]

end OQ7Prescribed
