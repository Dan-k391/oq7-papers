import work.PlanarLayerCompression

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarActiveAxisMaps_vector_current (L h θ : ℝ) (q : PlanarCurrentL2 L) :
    ∀ᵐ z : ℝ ∂volume,
      ((planarLayerAxisMap L h 1 (Real.cos θ) q : HeightL2) z) • basisC 0 +
        ((planarLayerAxisMap L h 0 (Real.sin θ) q : HeightL2) z) • basisC 1 =
          (q : HeightL2) z • complexify (if z < h then basisR 0 else rotatedAxis θ) := by
  filter_upwards [planarLayerAxisMap_coe L h 1 (Real.cos θ) q,
    planarLayerAxisMap_coe L h 0 (Real.sin θ) q] with z hc hs
  rw [hc, hs]
  by_cases hz : z < h
  · simp only [if_pos hz]
    ext i
    fin_cases i <;> simp [basisC, basisR, complexify]
  · simp only [if_neg hz]
    ext i
    fin_cases i <;> simp [basisC, rotatedAxis, complexify, mul_comm]

theorem planarActiveOutgoing_coe (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (q : PlanarCurrentL2 L) :
    (planarActiveOutgoing k hk L hL h θ q : HeightL2) =ᵐ[volume]
      (Icc 0 L).indicator (fun z =>
        if z < h then (k ^ 2 : ℝ) • scalarPlanarPotential k
          (planarLayerAxisMap L h 1 (Real.cos θ) q : HeightL2) z
        else (k ^ 2 : ℝ) • ((Real.cos θ : ℂ) * scalarPlanarPotential k
          (planarLayerAxisMap L h 1 (Real.cos θ) q : HeightL2) z +
            (Real.sin θ : ℂ) * scalarPlanarPotential k
              (planarLayerAxisMap L h 0 (Real.sin θ) q : HeightL2) z)) := by
  let C := planarLayerAxisMap L h 1 (Real.cos θ)
  let S := planarLayerAxisMap L h 0 (Real.sin θ)
  let T := planarScalarOutgoing k hk L hL
  let g := T (C q)
  let f := T (S q)
  have he : planarActiveOutgoing k hk L hL h θ q = C g + S f := by
    simp only [planarActiveOutgoing, planarLayerAxisMap_adjoint, ContinuousLinearMap.comp_apply, add_apply]
    rfl
  rw [he]
  filter_upwards [Lp.coeFn_add (C g : HeightL2) (S f : HeightL2),
    planarLayerAxisMap_coe L h 1 (Real.cos θ) g,
    planarLayerAxisMap_coe L h 0 (Real.sin θ) f,
    planarScalarOutgoing_coe k hk L hL (C q), planarScalarOutgoing_coe k hk L hL (S q)] with z ha hc hs hg hf
  change ((C g : HeightL2) + (S f : HeightL2)) z = _
  rw [ha]
  change (C g : HeightL2) z + (S f : HeightL2) z = _
  rw [hc, hs]
  change (if z < h then (1 : ℂ) * (g : HeightL2) z else (Real.cos θ : ℂ) * (g : HeightL2) z) +
    (if z < h then (0 : ℂ) * (f : HeightL2) z else (Real.sin θ : ℂ) * (f : HeightL2) z) = _
  rw [hg, hf]
  by_cases hm : z ∈ Icc 0 L <;> by_cases hz : z < h <;>
    simp [hm, hz, Complex.real_smul, mul_add, mul_assoc, mul_left_comm, C, S]

end OQ7Prescribed
