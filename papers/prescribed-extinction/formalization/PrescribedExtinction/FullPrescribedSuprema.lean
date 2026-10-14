import PrescribedExtinction.UniversalPassivity
import PrescribedExtinction.PrescribedExtinctionClass

noncomputable section
namespace OQ7Prescribed
open Set

theorem PrescribedExtinctionPair.absorptionDifference_lt_target {k P Q target : ℝ}
    (s : PrescribedExtinctionPair k P Q target) (hk : 0 < k) (htarget : 0 < target) :
    s.absorptionDifference < target := by
  have hp := scatteringState_positiveExtinction_absorption_pos k hk P Q s.body s.admissible .plus s.plus
    (by rw [s.plus_extinction]; exact htarget)
  have hm := scatteringState_positiveExtinction_absorption_pos k hk P Q s.body s.admissible .minus s.minus
    (by rw [s.minus_extinction]; exact htarget)
  have hpu := scatteringState_absorption_le_extinction k s.body .plus s.plus
  have hmu := scatteringState_absorption_le_extinction k s.body .minus s.minus
  rw [s.plus_extinction] at hpu
  rw [s.minus_extinction] at hmu
  unfold absorptionDifference
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem PrescribedExtinctionPair.asymmetry_lt_one {k P Q target : ℝ}
    (s : PrescribedExtinctionPair k P Q target) (hk : 0 < k) (htarget : 0 < target) :
    s.asymmetry < 1 := by
  have h := s.absorptionDifference_lt_target hk htarget
  rw [s.difference_eq_target_mul_asymmetry htarget] at h
  nlinarith

theorem PrescribedExtinctionPair.asymmetry_le_one {k P Q target : ℝ}
    (s : PrescribedExtinctionPair k P Q target) (hk : 0 < k) (htarget : 0 < target) :
    s.asymmetry ≤ 1 := (s.asymmetry_lt_one hk htarget).le

theorem prescribedExtinctionAsymmetryValues_isLUB (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    IsLUB (prescribedExtinctionAsymmetryValues k P Q target) 1 := by
  constructor
  · rintro g ⟨s, rfl⟩
    exact s.asymmetry_le_one hk htarget
  · exact prescribedExtinctionAsymmetryValues_upperBound_ge_one k P Q target hk hP hQ htarget

theorem prescribedExtinctionDifferenceValues_isLUB (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    IsLUB (prescribedExtinctionDifferenceValues k P Q target) target := by
  constructor
  · rintro d ⟨s, rfl⟩
    exact (s.absorptionDifference_lt_target hk htarget).le
  · exact prescribedExtinctionDifferenceValues_upperBound_ge_target k P Q target hk hP hQ htarget

theorem prescribedExtinctionAsymmetryValues_sSup (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    sSup (prescribedExtinctionAsymmetryValues k P Q target) = 1 :=
  (prescribedExtinctionAsymmetryValues_isLUB k P Q target hk hP hQ htarget).csSup_eq
    (prescribedExtinctionAsymmetryValues_nonempty k P Q target hk hP hQ htarget)

theorem prescribedExtinctionDifferenceValues_sSup (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    sSup (prescribedExtinctionDifferenceValues k P Q target) = target :=
  (prescribedExtinctionDifferenceValues_isLUB k P Q target hk hP hQ htarget).csSup_eq
    (prescribedExtinctionDifferenceValues_nonempty k P Q target hk hP hQ htarget)

theorem prescribedExtinctionAsymmetryValues_nonattainment (k P Q target : ℝ)
    (hk : 0 < k) (htarget : 0 < target) :
    1 ∉ prescribedExtinctionAsymmetryValues k P Q target := by
  rintro ⟨s, hs⟩
  have h := s.asymmetry_lt_one hk htarget
  rw [hs] at h
  exact (lt_irrefl 1) h

theorem prescribedExtinctionDifferenceValues_nonattainment (k P Q target : ℝ)
    (hk : 0 < k) (htarget : 0 < target) :
    target ∉ prescribedExtinctionDifferenceValues k P Q target := by
  rintro ⟨s, hs⟩
  have h := s.absorptionDifference_lt_target hk htarget
  rw [hs] at h
  exact (lt_irrefl target) h

/-- The complete prescribed-extinction supremum clause, over all original
admissible bodies and weak scattering states, with both sharp values and
universal strict nonattainment. -/
theorem prescribedExtinction_full_supremum (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    sSup (prescribedExtinctionAsymmetryValues k P Q target) = 1 ∧
      sSup (prescribedExtinctionDifferenceValues k P Q target) = target ∧
      (∀ s : PrescribedExtinctionPair k P Q target, s.asymmetry < 1 ∧ s.absorptionDifference < target) :=
  ⟨prescribedExtinctionAsymmetryValues_sSup k P Q target hk hP hQ htarget,
    prescribedExtinctionDifferenceValues_sSup k P Q target hk hP hQ htarget,
    fun s => ⟨s.asymmetry_lt_one hk htarget, s.absorptionDifference_lt_target hk htarget⟩⟩

end OQ7Prescribed
