import PrescribedExtinction.IsotropicPhysicalBody

noncomputable section
namespace OQ7Prescribed

theorem isotropicRankOneBody_admissible (B : TwoLayerBody) (ν θ P Q : ℝ) (α β : ℂ)
    (hν : 0 < ν) (ha : 0 ≤ α.re) (hb : 0 ≤ β.re)
    (haP : 1 + α.re ≤ P) (hbP : 1 + β.re ≤ P)
    (hα : 0 ≤ α.im) (hβ : 0 ≤ β.im) (hαQ : α.im + ν ≤ Q) (hβQ : β.im + ν ≤ Q) :
    (isotropicRankOneBody B ν θ α β).admissible P Q := by
  constructor
  · exact layerPermittivity_admissible P Q α.re α.im ν (basisR 0)
      (by simp [basisR, EuclideanSpace.norm_sq_eq]) ha haP hα hν hαQ
  · exact layerPermittivity_admissible P Q β.re β.im ν (rotatedAxis θ)
      (rotatedAxis_unit θ) hb hbP hβ hν hβQ

end OQ7Prescribed
