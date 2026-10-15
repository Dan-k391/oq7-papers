import PrescribedExtinction.PlanarSingleLayerCurrent

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarLayerL2Current_const_mul (k a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (F : PlanarLayerField k a b) (c : ℂ) :
    planarLayerL2Current k a b L ha hab hb (F.const_mul c) = c • planarLayerL2Current k a b L ha hab hb F := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [planarLayerL2Current_coe k a b L ha hab hb (F.const_mul c),
    planarLayerL2Current_coe k a b L ha hab hb F,
    Lp.coeFn_smul c (planarLayerL2Current k a b L ha hab hb F : HeightL2)] with z hc hf hs
  change (planarLayerL2Current k a b L ha hab hb (F.const_mul c) : HeightL2) z =
    (c • (planarLayerL2Current k a b L ha hab hb F : HeightL2) : HeightL2) z
  rw [hc, hs]
  change (Ioc a b).indicator (fun t => c * F.current t) z = c * (planarLayerL2Current k a b L ha hab hb F : HeightL2) z
  rw [hf]
  by_cases hm : z ∈ Ioc a b <;> simp [hm]

theorem planarLayerL2Current_add (k a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (F G : PlanarLayerField k a b) :
    planarLayerL2Current k a b L ha hab hb (F.add G) =
      planarLayerL2Current k a b L ha hab hb F + planarLayerL2Current k a b L ha hab hb G := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [planarLayerL2Current_coe k a b L ha hab hb (F.add G),
    planarLayerL2Current_coe k a b L ha hab hb F, planarLayerL2Current_coe k a b L ha hab hb G,
    Lp.coeFn_add (planarLayerL2Current k a b L ha hab hb F : HeightL2)
      (planarLayerL2Current k a b L ha hab hb G : HeightL2)] with z hc hf hg hs
  change (planarLayerL2Current k a b L ha hab hb (F.add G) : HeightL2) z =
    ((planarLayerL2Current k a b L ha hab hb F : HeightL2) + (planarLayerL2Current k a b L ha hab hb G : HeightL2)) z
  rw [hc, hs]
  change (Ioc a b).indicator (fun t => F.current t + G.current t) z =
    (planarLayerL2Current k a b L ha hab hb F : HeightL2) z + (planarLayerL2Current k a b L ha hab hb G : HeightL2) z
  rw [hf, hg]
  by_cases hm : z ∈ Ioc a b <;> simp [hm]

theorem scalarPlanarPotential_supported_smul (k : ℝ) (L : ℝ) (q : PlanarCurrentL2 L) (c : ℂ) (z : ℝ) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k ((c • q : PlanarCurrentL2 L) : HeightL2) z =
      c * ((k ^ 2 : ℝ) • scalarPlanarPotential k (q : HeightL2) z) := by
  have hs : ((c • q : PlanarCurrentL2 L) : HeightL2) =ᵐ[volume] fun t => c * (q : HeightL2) t :=
    Lp.coeFn_smul c (q : HeightL2)
  rw [scalarPlanarPotential_congr_ae k _ _ hs, scalarPlanarPotential_smul, Complex.real_smul, Complex.real_smul]
  ring

theorem scalarPlanarPotential_supported_add (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L)
    (q r : PlanarCurrentL2 L) (z : ℝ) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k ((q + r : PlanarCurrentL2 L) : HeightL2) z =
      (k ^ 2 : ℝ) • scalarPlanarPotential k (q : HeightL2) z +
        (k ^ 2 : ℝ) • scalarPlanarPotential k (r : HeightL2) z := by
  have hs : ((q + r : PlanarCurrentL2 L) : HeightL2) =ᵐ[volume] fun t => (q : HeightL2) t + (r : HeightL2) t :=
    Lp.coeFn_add (q : HeightL2) (r : HeightL2)
  have hiq : Integrable (q : HeightL2) volume := heightSupportedProfile_integrable L (planarHeightEmbedding L hL q)
  have hir : Integrable (r : HeightL2) volume := heightSupportedProfile_integrable L (planarHeightEmbedding L hL r)
  rw [scalarPlanarPotential_congr_ae k _ _ hs,
    scalarPlanarPotential_add k hk (q : HeightL2) (r : HeightL2) hiq hir, smul_add]

end OQ7Prescribed
