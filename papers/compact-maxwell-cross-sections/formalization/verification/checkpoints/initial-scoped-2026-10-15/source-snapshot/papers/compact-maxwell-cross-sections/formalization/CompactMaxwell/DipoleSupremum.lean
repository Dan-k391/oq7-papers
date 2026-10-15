import CompactMaxwell.SixVectorEquality

noncomputable section
open scoped ComplexOrder
namespace CompactMaxwell.DipoleSupremum
open Set GeneralizedResearch SixVectorBridge
open SixVectorEquality
def contrastValues : Set ℝ := {g | ∃ B : Mat, B.transpose = D * B * D ∧
  (Q B).PosSemidef ∧
  let U := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) B
  0 < dipoleWork U plus ∧
    g = |dipoleAbsorption U plus - dipoleAbsorption U (reversal.map plus)| / dipoleWork U plus}

theorem contrast_strict {g : ℝ} (hg : g ∈ contrastValues) : 0 ≤ g ∧ g < 1 := by
  obtain ⟨B, hr, hp, hW, rfl⟩ := hg
  have h := reciprocal_dipole_parabola reversal (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) B)
    (matrix_reciprocity B hr) (matrix_passivity B hp) plus incident_norm
  refine ⟨div_nonneg (abs_nonneg _) hW.le, (div_lt_one hW).mpr ?_⟩
  have hs : 0 < (dipoleWork (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) B) plus) ^ 2 :=
    sq_pos_of_pos hW
  linarith [h.2.2]

theorem near_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ g ∈ contrastValues, 1 - ε < g := by
  let t := 1 - ε
  let b := Real.sqrt ((1 - t ^ 2) / 2)
  have ht0 : -1 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hb : b ^ 2 = (1 - t ^ 2) / 2 := Real.sq_sqrt (by nlinarith)
  refine ⟨(1 + t) / 2, ?_, ?_⟩
  · refine ⟨A t b, reciprocal t b, passive hb, ?_, ?_⟩
    · change 0 < dipoleWork (T t b) plus
      rw [(works t b).1]
      linarith
    · change (1 + t) / 2 =
        |dipoleAbsorption (T t b) plus - dipoleAbsorption (T t b) (reversal.map plus)| /
          dipoleWork (T t b) plus
      rw [time_reverse, (absorptions hb).1, (absorptions hb).2,
        (works t b).1, sub_zero, abs_of_nonneg (by nlinarith : 0 ≤ (1 - t ^ 2) / 2)]
      apply (eq_div_iff (by linarith : 1 - t ≠ 0)).mpr
      ring
  · dsimp [t]
    linarith

theorem contrast_isLUB : IsLUB contrastValues 1 := by
  refine ⟨fun g hg => (contrast_strict hg).2.le, ?_⟩
  intro u hu
  by_contra hn
  have hlt : u < 1 := lt_of_not_ge hn
  let ε := min ((1 - u) / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨g, hg, hgl⟩ := near_one hε hε1
  have he := min_le_left ((1 - u) / 2) (1 / 2)
  have hgu := hu hg
  dsimp [ε] at hgl
  linarith

theorem free_extinction_supremum : sSup contrastValues = 1 ∧ 1 ∉ contrastValues := by
  have hne : contrastValues.Nonempty := by
    obtain ⟨g, hg, _⟩ := near_one (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨g, hg⟩
  refine ⟨contrast_isLUB.csSup_eq hne, ?_⟩
  intro h
  exact (lt_irrefl 1) (contrast_strict h).2

end CompactMaxwell.DipoleSupremum
