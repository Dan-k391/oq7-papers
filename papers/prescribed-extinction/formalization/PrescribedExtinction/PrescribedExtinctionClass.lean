import PrescribedExtinction.Theorem11

noncomputable section
namespace OQ7Prescribed
open Set

/-- The entire original admissible class at fixed common extinction. There
are no volume-equation or constructed-family restrictions on its states. -/
structure PrescribedExtinctionPair (k P Q target : ℝ) where
  body : TwoLayerBody
  admissible : body.admissible P Q
  plus : ScatteringState k body .plus
  minus : ScatteringState k body .minus
  plus_extinction : extinction k body .plus plus.electric = target
  minus_extinction : extinction k body .minus minus.electric = target

def PrescribedExtinctionPair.asymmetry {k P Q target : ℝ} (s : PrescribedExtinctionPair k P Q target) : ℝ :=
  normalizedAsymmetry k s.body s.plus.electric s.minus.electric

def PrescribedExtinctionPair.absorptionDifference {k P Q target : ℝ} (s : PrescribedExtinctionPair k P Q target) : ℝ :=
  |absorption k s.body s.plus.electric - absorption k s.body s.minus.electric|

def prescribedExtinctionAsymmetryValues (k P Q target : ℝ) : Set ℝ :=
  Set.range (PrescribedExtinctionPair.asymmetry (k := k) (P := P) (Q := Q) (target := target))

def prescribedExtinctionDifferenceValues (k P Q target : ℝ) : Set ℝ :=
  Set.range (PrescribedExtinctionPair.absorptionDifference (k := k) (P := P) (Q := Q) (target := target))

theorem PrescribedExtinctionPair.difference_eq_target_mul_asymmetry {k P Q target : ℝ}
    (s : PrescribedExtinctionPair k P Q target) (htarget : 0 < target) :
    s.absorptionDifference = target * s.asymmetry := by
  unfold absorptionDifference asymmetry normalizedAsymmetry
  rw [s.plus_extinction]
  field_simp [htarget.ne']

theorem prescribedExtinctionPair_approaches_one (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : PrescribedExtinctionPair k P Q target, 1 - ε < s.asymmetry ∧ s.asymmetry < 1 := by
  obtain ⟨B, hB, sp, sm, hp, hm, hΓ, hΓ1⟩ := theorem11 k P Q target hk hP hQ htarget ε hε hε1
  exact ⟨⟨B, hB, sp, sm, hp, hm⟩, hΓ, hΓ1⟩

theorem prescribedExtinctionAsymmetryValues_nonempty (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    (prescribedExtinctionAsymmetryValues k P Q target).Nonempty := by
  obtain ⟨s, _⟩ := prescribedExtinctionPair_approaches_one k P Q target hk hP hQ htarget
    (1 / 2) (by norm_num) (by norm_num)
  exact ⟨s.asymmetry, ⟨s, rfl⟩⟩

theorem prescribedExtinctionAsymmetryValues_above_every_lt_one (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target)
    (u : ℝ) (hu : u < 1) :
    ∃ g ∈ prescribedExtinctionAsymmetryValues k P Q target, u < g := by
  let ε := min ((1 - u) / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨s, hs, _⟩ := prescribedExtinctionPair_approaches_one k P Q target hk hP hQ htarget ε hε hε1
  refine ⟨s.asymmetry, ⟨s, rfl⟩, ?_⟩
  have he := min_le_left ((1 - u) / 2) (1 / 2)
  change 1 - min ((1 - u) / 2) (1 / 2) < s.asymmetry at hs
  linarith

theorem prescribedExtinctionAsymmetryValues_upperBound_ge_one (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target)
    (u : ℝ) (hu : u ∈ upperBounds (prescribedExtinctionAsymmetryValues k P Q target)) : 1 ≤ u := by
  by_contra hn
  obtain ⟨g, hg, hgu⟩ := prescribedExtinctionAsymmetryValues_above_every_lt_one k P Q target hk hP hQ htarget
    u (lt_of_not_ge hn)
  exact (not_lt_of_ge (hu hg)) hgu

theorem prescribedExtinctionDifferenceValues_nonempty (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target) :
    (prescribedExtinctionDifferenceValues k P Q target).Nonempty := by
  obtain ⟨s, _⟩ := prescribedExtinctionPair_approaches_one k P Q target hk hP hQ htarget
    (1 / 2) (by norm_num) (by norm_num)
  exact ⟨s.absorptionDifference, ⟨s, rfl⟩⟩

theorem prescribedExtinctionDifferenceValues_above_every_lt_target (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target)
    (u : ℝ) (hu : u < target) :
    ∃ d ∈ prescribedExtinctionDifferenceValues k P Q target, u < d := by
  obtain ⟨g, ⟨s, rfl⟩, hgu⟩ := prescribedExtinctionAsymmetryValues_above_every_lt_one k P Q target
    hk hP hQ htarget (u / target) ((div_lt_one htarget).mpr hu)
  refine ⟨s.absorptionDifference, ⟨s, rfl⟩, ?_⟩
  rw [s.difference_eq_target_mul_asymmetry htarget]
  have h := (div_lt_iff₀ htarget).mp hgu
  simpa only [mul_comm] using h

theorem prescribedExtinctionDifferenceValues_upperBound_ge_target (k P Q target : ℝ)
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (htarget : 0 < target)
    (u : ℝ) (hu : u ∈ upperBounds (prescribedExtinctionDifferenceValues k P Q target)) : target ≤ u := by
  by_contra hn
  obtain ⟨d, hd, hdu⟩ := prescribedExtinctionDifferenceValues_above_every_lt_target k P Q target hk hP hQ htarget
    u (lt_of_not_ge hn)
  exact (not_lt_of_ge (hu hd)) hdu

end OQ7Prescribed
