import work.PlanarSlabCoupledEquations

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem relativePermittivity_susceptibility_im (A : OQ7.HomogeneousLayer) :
    (OQ7.relativePermittivity A - 1).im = A.q := by simp [OQ7.relativePermittivity]

theorem relativePermittivity_susceptibility_ne_zero (A : OQ7.HomogeneousLayer) (hq : 0 < A.q) :
    OQ7.relativePermittivity A - 1 ≠ 0 := by
  intro hz
  have h := congrArg Complex.im hz
  rw [relativePermittivity_susceptibility_im] at h
  simp only [Complex.zero_im] at h
  linarith

theorem slabCoupledCurrent_eq_planarNormalizedResponse (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 < A.q) (hqW : 0 < W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) :
    slabCoupledCurrent k A W θ σ hpA hpW hdA hdW =
      planarNormalizedResponse k hk σ (A.width + W.width) (by linarith) A.width θ
        (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
        (by simpa only [relativePermittivity_susceptibility_im] using hqA)
        (by simpa only [relativePermittivity_susceptibility_im] using hqW) := by
  have hα : 0 < (OQ7.relativePermittivity A - 1).im := by
    simpa only [relativePermittivity_susceptibility_im] using hqA
  have hβ : 0 < (OQ7.relativePermittivity W - 1).im := by
    simpa only [relativePermittivity_susceptibility_im] using hqW
  apply (planarActiveMaterialEquiv k hk (A.width + W.width) (by linarith) A.width θ
    (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1) hα hβ).injective
  change planarActiveMaterialOperator k hk (A.width + W.width) (by linarith) A.width θ
    (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
    (slabCoupledCurrent k A W θ σ hpA hpW hdA hdW) = _
  rw [slabCoupledCurrent_material_equation k hk A W θ σ hpA hpW hqA.le hqW.le hdA hdW
    (relativePermittivity_susceptibility_ne_zero A hqA) (relativePermittivity_susceptibility_ne_zero W hqW)]
  exact (planarNormalizedResponse_equation k hk σ (A.width + W.width) (by linarith) A.width θ
    (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1) hα hβ).symm

end OQ7Prescribed
