import PrescribedExtinction.PhysicalTheorem11

/-! Auditor's independent experiments for frozen commit 686402a (not from the repo). -/
open MeasureTheory Set Filter
open OQ7Prescribed

noncomputable section

/-! ## A0. Exact declaration and axioms -/
#check @OQ7Prescribed.theorem11_complete
#print axioms OQ7Prescribed.theorem11_complete
example : OQ7Prescribed.PhysicalTheorem11Statement := OQ7Prescribed.theorem11_complete
-- The preserved existence statement is literally the first conjunct.
example : PhysicalTheorem11Statement → Theorem11Statement := fun h => h.1

/-! ## A1. Consequences extracted from the statement exactly as the manuscript phrases them. -/
theorem auditor_sup_is_lub (k P Q E : ℝ) (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hE : 0 < E) :
    (∀ s : PrescribedExtinctionPair k P Q E, s.asymmetry ≤ 1) ∧
    (∀ ε > 0, ∃ s : PrescribedExtinctionPair k P Q E, 1 - ε < s.asymmetry) ∧
    (∀ s : PrescribedExtinctionPair k P Q E, s.asymmetry < 1) := by
  obtain ⟨-, h⟩ := theorem11_complete
  obtain ⟨hsup, -, -, -, hlt⟩ := h k P Q E hk hP hQ hE
  have hne : (prescribedExtinctionAsymmetryValues k P Q E).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn, Real.sSup_empty] at hsup
    norm_num at hsup
  have hbdd : BddAbove (prescribedExtinctionAsymmetryValues k P Q E) := by
    by_contra hb
    rw [Real.sSup_of_not_bddAbove hb] at hsup
    norm_num at hsup
  refine ⟨fun s => ?_, fun ε hε => ?_, fun s => (hlt s).1⟩
  · rw [← hsup]; exact le_csSup hbdd ⟨s, rfl⟩
  · obtain ⟨g, ⟨s, rfl⟩, hg⟩ := exists_lt_of_lt_csSup hne (show 1 - ε < sSup _ by rw [hsup]; linarith)
    exact ⟨s, hg⟩

/-! ## A2. Positivity of X for EVERY admissible body and EVERY state
(manuscript p.3, "X = X₊ = X₋ > 0"). Not stated in the repo; proved here. -/
def auditorZeroPolarization (p : CompactPolarization) : CompactPolarization where
  current := 0
  radius := p.radius
  radius_nonneg := p.radius_nonneg
  memLp := MemLp.zero
  vanish := fun _ _ => rfl

theorem auditor_extinction_pos (k : ℝ) (hk : 0 < k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (σ : Direction) (s : ScatteringState k B σ) :
    0 < extinction k B σ s.electric := by
  have hX0 := scatteringState_extinction_nonneg k hk.le P Q B hB σ s
  refine lt_of_le_of_ne hX0 (fun hX => ?_)
  have hA0 := physicalAbsorption_nonneg k hk.le P Q B hB s.electric
  have hAX := scatteringState_absorption_le_extinction k B σ s
  have hA : absorption k B s.electric = 0 := by linarith
  -- absorption zero + strict loss ⇒ E = 0 a.e. on the body
  have hi := physicalAbsorption_integrable B s.electric s.maxwell.1
  have hn : ∀ᵐ x ∂(volume.restrict B.domain), 0 ≤ (quadratic (B.permittivity x) (s.electric x)).im := by
    filter_upwards [ae_restrict_mem (bodyDomain_isOpen B).measurableSet] with x hx
    exact material_quadratic_im_nonneg P Q _ (bodyPermittivity_admissible_on_domain P Q B hB x hx) _
  have hz : (∫ x in B.domain, (quadratic (B.permittivity x) (s.electric x)).im) = 0 :=
    (mul_eq_zero.mp hA).resolve_left hk.ne'
  have hq := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  have hzero : s.electric =ᵐ[volume.restrict B.domain] 0 := by
    filter_upwards [ae_restrict_mem (bodyDomain_isOpen B).measurableSet, hq] with x hx hqx
    by_contra he
    have ht := (bodyPermittivity_admissible_on_domain P Q B hB x hx).2.2.1 (s.electric x) he
    change (quadratic (B.permittivity x) (s.electric x)).im = 0 at hqx
    rw [hqx] at ht
    exact (lt_irrefl 0) ht
  -- hence the polarization vanishes a.e. on ℝ³
  set p := physicalCompactPolarization B s.electric s.maxwell.1 with hpdef
  have hpz : p.current =ᵐ[volume] (auditorZeroPolarization p).current := by
    have h1 : ∀ᵐ x ∂volume, x ∈ B.domain → s.electric x = 0 :=
      (ae_restrict_iff' (bodyDomain_isOpen B).measurableSet).mp hzero
    filter_upwards [h1] with x hx
    change polarization B s.electric x = 0
    by_cases hxd : x ∈ B.domain
    · simp [polarization, hx hxd, tensorApply]
    · exact polarization_zero_outside B s.electric x hxd
  -- the radiated field of a zero current is zero a.e.
  have hfield : outgoingElectricField k p =ᵐ[volume] 0 := by
    refine (outgoingElectricField_eq_ae k p).trans ?_
    rw [electricVolumeField_congr_current k p (auditorZeroPolarization p) hpz]
    have hL : (auditorZeroPolarization p).memLp.toLp (auditorZeroPolarization p).current = 0 :=
      MemLp.toLp_zero _
    have hR : remainderPotential k (auditorZeroPolarization p) = 0 := by
      funext x
      simp [remainderPotential, auditorZeroPolarization, MeasureTheory.convolution]
    filter_upwards [Lp.coeFn_zero Vector 2 (volume : Measure Position)] with x hx
    simp only [electricVolumeField, hL, hR, map_zero, Pi.zero_apply, add_zero]
    exact hx
  -- representation: E = f + E_s a.e., so E = f a.e. on the body
  have hrep := (scatteringState_outgoing_volume_representation k hk B σ s).1
  have hf : s.electric =ᵐ[volume] incidentElectric k σ := by
    filter_upwards [hrep, hfield] with x h1 h2
    rw [h1]
    change incidentElectric k σ x + outgoingElectricField k p x = _
    rw [h2]; simp
  have hcontra : ∀ᵐ x ∂(volume.restrict B.domain), False := by
    filter_upwards [hzero, ae_restrict_of_ae hf] with x h0 h1
    have hn1 : ‖incidentElectric k σ x‖ = 1 := incidentElectric_norm k σ x
    rw [← h1, h0] at hn1
    simp at hn1
  have hpos : 0 < volume B.domain := by
    refine (bodyDomain_isOpen B).measure_pos volume
      ⟨WithLp.toLp 2 ![0, 0, (B.absorberThickness + B.plateThickness) / 2], ?_⟩
    have := B.aperture_pos; have := B.absorberThickness_pos; have := B.plateThickness_pos
    simp only [TwoLayerBody.domain, bodyDomain, squareAperture, Set.mem_setOf_eq]
    simp
    repeat' constructor
    all_goals (first | linarith | positivity)
  have h0 : volume.restrict B.domain = 0 := by
    rw [← Measure.measure_univ_eq_zero]
    have := ae_iff.mp hcontra
    simpa using this
  rw [Measure.restrict_eq_zero] at h0
  exact (ne_of_gt hpos) h0

/-! ## A3. Hence universal strict nonattainment holds for EVERY admissible body with no
positivity hypothesis (the X = 0 / division-by-zero branch is vacuous). -/
theorem auditor_universal_gamma_lt_one (k : ℝ) (hk : 0 < k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus) :
    normalizedAsymmetry k B sp.electric sm.electric < 1 :=
  universal_physical_asymmetry_lt_one k hk P Q B hB sp sm (auditor_extinction_pos k hk P Q B hB .plus sp)

#print axioms auditor_sup_is_lub
#print axioms auditor_extinction_pos
#print axioms auditor_universal_gamma_lt_one
