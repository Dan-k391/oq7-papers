import work.PhysicalIsotropicPrescribedExtinction
import work.IsotropicPhysicalAdmissibility
import PrescribedExtinction.PlanarPrescribedDesign

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

/-- The exact physical prescribed-extinction theorem, with actual weak Maxwell
fields, full uniform outgoing radiation, and strictly admissible tensors. -/
theorem theorem11 : Theorem11Statement := by
  intro k P Q target hk hP hQ htarget ε hε hεone
  obtain ⟨A, W, hpA, hpW, hqA, hqW, hdA, hdW, hAp, hWp, hAq, hWq, hdesign⟩ :=
    exists_planar_design_near_unit_asymmetry k hk P Q ε hP hQ hε
  let α := OQ7.relativePermittivity A - 1
  let β := OQ7.relativePermittivity W - 1
  have hα : 0 < α.im := by simpa only [α, relativePermittivity_susceptibility_im] using hqA
  have hβ : 0 < β.im := by simpa only [β, relativePermittivity_susceptibility_im] using hqW
  obtain ⟨B, ν, θ, _, _, hν, hνQ, _, hL, hXp, hXm, hG, hG1⟩ :=
    physicalIsotropic_prescribedExtinctionOfPlanarDesign k hk A.width W.width hdA hdW α β hα hβ
      target (1 - ε) (Q / 3) htarget (by positivity) hdesign
  have hreA : α.re = A.p - 1 := by simp [α, OQ7.relativePermittivity]
  have hreW : β.re = W.p - 1 := by simp [β, OQ7.relativePermittivity]
  have himA : α.im = A.q := relativePermittivity_susceptibility_im A
  have himW : β.im = W.q := relativePermittivity_susceptibility_im W
  have hadm : (isotropicRankOneBody B ν θ α β).admissible P Q :=
    isotropicRankOneBody_admissible B ν θ P Q α β hν
      (by rw [hreA]; linarith) (by rw [hreW]; linarith)
      (by rw [hreA]; linarith) (by rw [hreW]; linarith) hα.le hβ.le
      (by rw [himA]; linarith) (by rw [himW]; linarith)
  let p := bodyCurrentPolarization B (physicalPerturbedCurrent k B .plus ν θ α β)
  let q := bodyCurrentPolarization B (physicalPerturbedCurrent k B .minus ν θ α β)
  let sp := scatteringStateOfVolumeEquation k (isotropicRankOneBody B ν θ α β) .plus p
    (physicalPerturbedCurrent_physicalVolumeEquation k B .plus ν θ α β hL)
  let sm := scatteringStateOfVolumeEquation k (isotropicRankOneBody B ν θ α β) .minus q
    (physicalPerturbedCurrent_physicalVolumeEquation k B .minus ν θ α β hL)
  refine ⟨isotropicRankOneBody B ν θ α β, hadm, sp, sm, ?_, ?_, ?_, ?_⟩
  · exact (physicalPerturbedExtinction_eq_original k B .plus ν θ α β hL).symm.trans hXp
  · exact (physicalPerturbedExtinction_eq_original k B .minus ν θ α β hL).symm.trans hXm
  · change 1 - ε < normalizedAsymmetry k (isotropicRankOneBody B ν θ α β)
      (volumeTotalElectric k .plus p) (volumeTotalElectric k .minus q)
    rw [← physicalPerturbedAsymmetry_eq_original k B ν θ α β hL]
    exact hG
  · change normalizedAsymmetry k (isotropicRankOneBody B ν θ α β)
      (volumeTotalElectric k .plus p) (volumeTotalElectric k .minus q) < 1
    rw [← physicalPerturbedAsymmetry_eq_original k B ν θ α β hL]
    exact hG1

end OQ7Prescribed
