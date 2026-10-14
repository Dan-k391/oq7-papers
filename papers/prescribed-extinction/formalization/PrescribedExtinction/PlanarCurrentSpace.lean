import PrescribedExtinction.PlanarHeightMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

abbrev PlanarCurrentL2 (L : ℝ) := SetSupportedL2 (E := ℂ) (volume : Measure ℝ) (Icc 0 L)

instance planarCurrentL2_completeSpace (L : ℝ) : CompleteSpace (PlanarCurrentL2 L) := by
  let : IsClosed (setSupportedL2 (E := ℂ) (volume : Measure ℝ) (Icc 0 L) : Set HeightL2) :=
    setSupportedL2_isClosed volume (Icc 0 L) measurableSet_Icc
  exact inferInstance

def planarHeightEmbeddingLinear (L : ℝ) (hL : 0 ≤ L) : PlanarCurrentL2 L →ₗ[ℂ] HeightSupportedL2 L where
  toFun q := ⟨(q : HeightL2), by
    change ∀ᵐ z : ℝ ∂volume, z ∉ Icc (-L) L → (q : HeightL2) z = 0
    filter_upwards [q.property] with z hz
    intro hn
    apply hz
    intro hm
    exact hn ⟨by linarith [hm.1], hm.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def planarHeightEmbedding (L : ℝ) (hL : 0 ≤ L) : PlanarCurrentL2 L →L[ℂ] HeightSupportedL2 L :=
  (planarHeightEmbeddingLinear L hL).mkContinuous 1 fun q => by
    change ‖q‖ ≤ 1 * ‖q‖
    simp

theorem planarHeightEmbedding_norm (L : ℝ) (hL : 0 ≤ L) (q : PlanarCurrentL2 L) :
    ‖planarHeightEmbedding L hL q‖ = ‖q‖ := rfl

def planarScalarOutgoingLinear (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) :
    PlanarCurrentL2 L →ₗ[ℂ] PlanarCurrentL2 L where
  toFun q := ⟨(k ^ 2 : ℝ) • planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q), by
    change ∀ᵐ z : ℝ ∂volume, z ∉ Icc 0 L →
      ((k ^ 2 : ℝ) • planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)) z = 0
    filter_upwards [Lp.coeFn_smul (k ^ 2 : ℝ) (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)),
      planarHeightMap_coe k hk L L hL hL (planarHeightEmbedding L hL q)] with z hs hp
    intro hn
    rw [hs]
    change (k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)) z = 0
    rw [hp, indicator_of_notMem hn, smul_zero]⟩
  map_add' q r := Subtype.ext (by
    change (k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL (q + r))) =
      (k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)) +
        (k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL r))
    rw [map_add, map_add, smul_add])
  map_smul' a q := Subtype.ext (by
    change (k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL (a • q))) =
      a • ((k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)))
    rw [map_smul, map_smul, smul_comm])

def planarScalarOutgoing (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) :
    PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L :=
  (planarScalarOutgoingLinear k hk L hL).mkContinuous
    (k ^ 2 * (Real.sqrt L * (1 / (2 * k)) * Real.sqrt (2 * L))) fun q => by
      change ‖(k ^ 2 : ℝ) • planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg k)]
      exact (mul_le_mul_of_nonneg_left
        (planarHeightRaw_norm_le k hk L L hL hL (planarHeightEmbedding L hL q)) (sq_nonneg k)).trans_eq (by
          rw [planarHeightEmbedding_norm]
          ring)

theorem planarScalarOutgoing_coe (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (q : PlanarCurrentL2 L) :
    (planarScalarOutgoing k hk L hL q : HeightL2) =ᵐ[volume]
      (Icc 0 L).indicator (fun z => (k ^ 2 : ℝ) • scalarPlanarPotential k (q : HeightL2) z) := by
  filter_upwards [Lp.coeFn_smul (k ^ 2 : ℝ) (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)),
    planarHeightMap_coe k hk L L hL hL (planarHeightEmbedding L hL q)] with z hs hp
  change ((k ^ 2 : ℝ) • planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)) z = _
  rw [hs]
  change (k ^ 2 : ℝ) • (planarHeightMap k hk L L hL hL (planarHeightEmbedding L hL q)) z = _
  rw [hp]
  by_cases hm : z ∈ Icc 0 L
  · simp only [indicator_of_mem hm]; rfl
  · simp only [indicator_of_notMem hm, smul_zero]

end OQ7Prescribed
