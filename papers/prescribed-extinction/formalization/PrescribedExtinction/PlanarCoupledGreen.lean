import PrescribedExtinction.PlanarLayerAxisSupport

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarLayerAxisMap_cos_sin_combination (L h θ : ℝ) (q : PlanarCurrentL2 L) :
    planarLayerAxisMap L h (Real.cos θ) 1 q =
      (Real.cos θ : ℂ) • planarLayerAxisMap L h 1 (Real.cos θ) q +
        (Real.sin θ : ℂ) • planarLayerAxisMap L h 0 (Real.sin θ) q := by
  let C := planarLayerAxisMap L h 1 (Real.cos θ)
  let S := planarLayerAxisMap L h 0 (Real.sin θ)
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [planarLayerAxisMap_coe L h (Real.cos θ) 1 q,
    planarLayerAxisMap_coe L h 1 (Real.cos θ) q,
    planarLayerAxisMap_coe L h 0 (Real.sin θ) q,
    Lp.coeFn_add ((Real.cos θ : ℂ) • (C q : HeightL2)) ((Real.sin θ : ℂ) • (S q : HeightL2)),
    Lp.coeFn_smul (Real.cos θ : ℂ) (C q : HeightL2),
    Lp.coeFn_smul (Real.sin θ : ℂ) (S q : HeightL2)] with z hd hc hs ha hcm hsm
  change (planarLayerAxisMap L h (Real.cos θ) 1 q : HeightL2) z =
    (((Real.cos θ : ℂ) • (C q : HeightL2)) + ((Real.sin θ : ℂ) • (S q : HeightL2))) z
  rw [hd, ha]
  change _ = ((Real.cos θ : ℂ) • (C q : HeightL2) : HeightL2) z +
    ((Real.sin θ : ℂ) • (S q : HeightL2) : HeightL2) z
  rw [hcm, hsm]
  change _ = (Real.cos θ : ℂ) * (C q : HeightL2) z + (Real.sin θ : ℂ) * (S q : HeightL2) z
  rw [hc, hs]
  by_cases hz : z < h
  · simp only [if_pos hz, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  · simp only [if_neg hz, Complex.ofReal_one, one_mul]
    have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    linear_combination -(q : HeightL2) z * hcs

theorem planarActiveOutgoing_two_layer_current_eq (k : ℝ) (hk : 0 < k) (h L : ℝ)
    (hh : 0 ≤ h) (hL : h ≤ L) (θ : ℝ) (F : PlanarLayerField k 0 h) (G : PlanarLayerField k h L) :
    planarActiveOutgoing k hk L (hh.trans hL) h θ
        (planarLayerL2Current k 0 h L le_rfl hh hL F + planarLayerL2Current k h L L hh hL le_rfl G) =
      planarLayerAxisMap L h 1 (Real.cos θ)
        (planarScalarOutgoing k hk L (hh.trans hL) (planarLayerL2Current k 0 h L le_rfl hh hL F)) +
      planarLayerAxisMap L h (Real.cos θ) 1
        (planarScalarOutgoing k hk L (hh.trans hL) (planarLayerL2Current k h L L hh hL le_rfl G)) := by
  let A := planarLayerL2Current k 0 h L le_rfl hh hL F
  let W := planarLayerL2Current k h L L hh hL le_rfl G
  let C := planarLayerAxisMap L h 1 (Real.cos θ)
  let S := planarLayerAxisMap L h 0 (Real.sin θ)
  let T := planarScalarOutgoing k hk L (hh.trans hL)
  have hC : C (A + W) = A + (Real.cos θ : ℂ) • W := by
    rw [map_add, planarLayerAxisMap_first_current, planarLayerAxisMap_second_current, Complex.ofReal_one, one_smul]
  have hS : S (A + W) = (Real.sin θ : ℂ) • W := by
    rw [map_add, planarLayerAxisMap_first_current, planarLayerAxisMap_second_current, Complex.ofReal_zero, zero_smul, zero_add]
  unfold planarActiveOutgoing
  rw [planarLayerAxisMap_adjoint, planarLayerAxisMap_adjoint]
  change C (T (C (A + W))) + S (T (S (A + W))) = C (T A) + planarLayerAxisMap L h (Real.cos θ) 1 (T W)
  rw [hC, hS]
  simp only [map_add, map_smul]
  rw [planarLayerAxisMap_cos_sin_combination, add_assoc]

theorem planarActiveOutgoing_two_layer_current_coe (k : ℝ) (hk : 0 < k) (h L : ℝ)
    (hh : 0 ≤ h) (hL : h ≤ L) (θ : ℝ) (F : PlanarLayerField k 0 h) (G : PlanarLayerField k h L) :
    (planarActiveOutgoing k hk L (hh.trans hL) h θ
      (planarLayerL2Current k 0 h L le_rfl hh hL F + planarLayerL2Current k h L L hh hL le_rfl G) : HeightL2) =ᵐ[volume]
    (Icc 0 L).indicator (fun z =>
      if z < h then
        (k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2) z +
        (Real.cos θ : ℂ) * ((k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k h L L hh hL le_rfl G : HeightL2) z)
      else
        (Real.cos θ : ℂ) * ((k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k 0 h L le_rfl hh hL F : HeightL2) z) +
        (k ^ 2 : ℝ) • scalarPlanarPotential k (planarLayerL2Current k h L L hh hL le_rfl G : HeightL2) z) := by
  let A := planarLayerL2Current k 0 h L le_rfl hh hL F
  let W := planarLayerL2Current k h L L hh hL le_rfl G
  let T := planarScalarOutgoing k hk L (hh.trans hL)
  let C := planarLayerAxisMap L h 1 (Real.cos θ)
  let D := planarLayerAxisMap L h (Real.cos θ) 1
  rw [planarActiveOutgoing_two_layer_current_eq]
  filter_upwards [Lp.coeFn_add (C (T A) : HeightL2) (D (T W) : HeightL2),
    planarLayerAxisMap_coe L h 1 (Real.cos θ) (T A),
    planarLayerAxisMap_coe L h (Real.cos θ) 1 (T W),
    planarScalarOutgoing_coe k hk L (hh.trans hL) A,
    planarScalarOutgoing_coe k hk L (hh.trans hL) W] with z ha hc hd htA htW
  change ((C (T A) : HeightL2) + (D (T W) : HeightL2)) z = _
  rw [ha]
  change (C (T A) : HeightL2) z + (D (T W) : HeightL2) z = _
  rw [hc, hd]
  change (if z < h then (1 : ℂ) * (T A : HeightL2) z else (Real.cos θ : ℂ) * (T A : HeightL2) z) +
    (if z < h then (Real.cos θ : ℂ) * (T W : HeightL2) z else (1 : ℂ) * (T W : HeightL2) z) = _
  rw [htA, htW]
  by_cases hm : z ∈ Icc 0 L <;> by_cases hz : z < h <;> simp [hm, hz, A, W]

end OQ7Prescribed
