import PrescribedExtinction.ArbitraryStateOpticalBalance
import PrescribedExtinction.FullPrescribedSuprema

noncomputable section
namespace OQ7Prescribed

theorem admissibleScatteringState_extinction_reciprocity (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus) :
    extinction k B .plus sp.electric = extinction k B .minus sm.electric :=
  scatteringState_extinction_reciprocity k hk B hB.1.1 hB.2.1 sp sm

def prescribedExtinctionPairOfPlus (k : ℝ) (hk : 0 < k) (P Q target : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus)
    (hX : extinction k B .plus sp.electric = target) : PrescribedExtinctionPair k P Q target where
  body := B
  admissible := hB
  plus := sp
  minus := sm
  plus_extinction := hX
  minus_extinction := (admissibleScatteringState_extinction_reciprocity k hk P Q B hB sp sm).symm.trans hX

theorem universal_physical_asymmetry_lt_one (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus)
    (hX : 0 < extinction k B .plus sp.electric) :
    normalizedAsymmetry k B sp.electric sm.electric < 1 := by
  let s := prescribedExtinctionPairOfPlus k hk P Q (extinction k B .plus sp.electric) B hB sp sm rfl
  exact s.asymmetry_lt_one hk hX

theorem universal_physical_asymmetry_nonneg (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus) :
    0 ≤ normalizedAsymmetry k B sp.electric sm.electric :=
  physicalAsymmetry_nonneg k B _ _ (scatteringState_extinction_nonneg k hk.le P Q B hB .plus sp)

theorem universal_physical_asymmetry_le_one (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus) :
    normalizedAsymmetry k B sp.electric sm.electric ≤ 1 := by
  by_cases hz : extinction k B .plus sp.electric = 0
  · simp [normalizedAsymmetry, hz]
  · have hx : 0 < extinction k B .plus sp.electric :=
      lt_of_le_of_ne (scatteringState_extinction_nonneg k hk.le P Q B hB .plus sp) (Ne.symm hz)
    exact (universal_physical_asymmetry_lt_one k hk P Q B hB sp sm hx).le

theorem universal_physical_absorptionDifference_lt_extinction (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus)
    (hX : 0 < extinction k B .plus sp.electric) :
    |absorption k B sp.electric - absorption k B sm.electric| < extinction k B .plus sp.electric := by
  let s := prescribedExtinctionPairOfPlus k hk P Q (extinction k B .plus sp.electric) B hB sp sm rfl
  exact s.absorptionDifference_lt_target hk hX

theorem scatteringState_absorption_lt_extinction (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (σ : Direction) (s : ScatteringState k B σ)
    (hX : 0 < extinction k B σ s.electric) : absorption k B s.electric < extinction k B σ s.electric := by
  have hS := positiveExtinction_scattering_pos k hk B s.electric s.maxwell.1 σ hX
  have he := scatteringState_energy_balance k hk B σ s
  linarith

theorem universal_physical_asymmetry_eq_scattering_difference (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus) :
    normalizedAsymmetry k B sp.electric sm.electric =
      |scattering k B sp.electric - scattering k B sm.electric| / extinction k B .plus sp.electric := by
  have hp := scatteringState_energy_balance k hk B .plus sp
  have hm := scatteringState_energy_balance k hk B .minus sm
  have hx := admissibleScatteringState_extinction_reciprocity k hk P Q B hB sp sm
  have hd : absorption k B sp.electric - absorption k B sm.electric =
      -(scattering k B sp.electric - scattering k B sm.electric) := by linarith
  unfold normalizedAsymmetry
  rw [hd, abs_neg]

end OQ7Prescribed
