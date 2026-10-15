import PrescribedExtinction.PhysicalTheorem11

/-! The unrestricted compact-dielectric theorem is an explicit corollary of
the stronger, source-pinned prescribed-extinction result. This does not certify
the independent general-stack localization proof in Sections 5 and 6. -/
noncomputable section
namespace CompactMaxwell.PhysicalSupremum
open OQ7Prescribed Set

theorem unrestricted_examples (k P Q ε : ℝ) (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ B : TwoLayerBody, B.admissible P Q ∧
      ∃ sp : ScatteringState k B .plus, ∃ sm : ScatteringState k B .minus,
        extinction k B .plus sp.electric = extinction k B .minus sm.electric ∧
        0 < extinction k B .plus sp.electric ∧
        1 - ε < normalizedAsymmetry k B sp.electric sm.electric ∧
        normalizedAsymmetry k B sp.electric sm.electric < 1 := by
  obtain ⟨B, hB, sp, sm, hp, hm, hlow, hhigh⟩ :=
    theorem11_complete.1 k P Q 1 hk hP hQ (by norm_num) ε hε hε1
  exact ⟨B, hB, sp, sm, hp.trans hm.symm, by rw [hp]; norm_num, hlow, hhigh⟩

def asymmetryValues (k P Q : ℝ) : Set ℝ := {g | ∃ B : TwoLayerBody,
  B.admissible P Q ∧ ∃ sp : ScatteringState k B .plus, ∃ sm : ScatteringState k B .minus,
    0 < extinction k B .plus sp.electric ∧
      g = normalizedAsymmetry k B sp.electric sm.electric}

theorem universal_strict {k P Q g : ℝ} (hk : 0 < k) (hg : g ∈ asymmetryValues k P Q) :
    g < 1 := by
  obtain ⟨B, hB, sp, sm, hX, rfl⟩ := hg
  exact universal_physical_asymmetry_lt_one k hk P Q B hB sp sm hX

theorem unrestricted_isLUB (k P Q : ℝ) (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) :
    IsLUB (asymmetryValues k P Q) 1 := by
  refine ⟨fun g hg => (universal_strict hk hg).le, ?_⟩
  intro u hu
  by_contra hn
  have hlt : u < 1 := lt_of_not_ge hn
  let ε := min ((1 - u) / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨B, hB, sp, sm, _, hX, hlow, _⟩ := unrestricted_examples k P Q ε hk hP hQ hε hε1
  have hg : normalizedAsymmetry k B sp.electric sm.electric ∈ asymmetryValues k P Q :=
    ⟨B, hB, sp, sm, hX, rfl⟩
  have hgu := hu hg
  have he := min_le_left ((1 - u) / 2) (1 / 2)
  dsimp [ε] at hlow
  linarith

theorem unrestricted_compact_dielectric_supremum (k P Q : ℝ) (hk : 0 < k)
    (hP : 1 < P) (hQ : 0 < Q) :
    sSup (asymmetryValues k P Q) = 1 ∧ 1 ∉ asymmetryValues k P Q := by
  have hne : (asymmetryValues k P Q).Nonempty := by
    obtain ⟨B, hB, sp, sm, _, hX, _, _⟩ := unrestricted_examples k P Q (1 / 2)
      hk hP hQ (by norm_num) (by norm_num)
    exact ⟨_, ⟨B, hB, sp, sm, hX, rfl⟩⟩
  refine ⟨(unrestricted_isLUB k P Q hk hP hQ).csSup_eq hne, ?_⟩
  intro h
  exact (lt_irrefl 1) (universal_strict hk h)

end CompactMaxwell.PhysicalSupremum
