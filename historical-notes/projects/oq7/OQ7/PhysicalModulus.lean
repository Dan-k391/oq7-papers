import OQ7.ModulusComparison
import OQ7.PhysicalGram
import OQ7.PhysicalClass

noncomputable section
namespace OQ7
open Set
open scoped Topology

/-- Lemma 4.1 for the actual finite-layer fundamental field.
Only the selected propagation interval must satisfy the chosen real-permittivity cap;
the exterior finite passive multilayer may have different global material bounds. -/
theorem stackFundamentalSolution_modulus_comparison {k P Pglobal Qglobal x h : ℝ}
    (hk : 0 < k) (hP : 0 < P) {layers : List HomogeneousLayer}
    (hlayers : StackAdmissible Pglobal Qglobal layers)
    (hh : 0 ≤ h) (hmax : h ≤ Real.pi / (k * Real.sqrt P))
    (hlocal : ∀ z ∈ Ioo x (x + h), stackRealProfile layers z ≤ P) :
    Real.sin (k * Real.sqrt P * h) / (k * Real.sqrt P) ≤
      ‖stackFundamentalSolution k layers (x + h) x‖ := by
  classical
  rcases hh.eq_or_lt with hh | hh
  · rw [← hh]
    simp [stackFundamentalSolution_initial k hlayers]
  · let v := stackFundamentalState k layers x
    let s := fun t : ℝ => stackFundamentalSolution k layers (x + t) x
    let ds := fun t : ℝ => Complex.I * (k : ℂ) * stackMagneticField k layers v (x + t)
    let p := fun t : ℝ => stackRealProfile layers (x + t)
    let q := fun t : ℝ => stackLossProfile layers (x + t)
    let bad := (interfacePositions layers).toFinset.image (fun z => z - x)
    have hK : 0 < k * Real.sqrt P := mul_pos hk (Real.sqrt_pos.mpr hP)
    have hKh : k * Real.sqrt P * h ≤ Real.pi := by
      have hb := (le_div_iff₀ hK).mp hmax
      nlinarith
    have hscont : Continuous s :=
      (stackElectricField_continuous k hlayers v).comp (continuous_const.add continuous_id)
    have hdscont : Continuous ds :=
      ((stackMagneticField_continuous k hlayers v).comp
        (continuous_const.add continuous_id)).const_mul (Complex.I * (k : ℂ))
    have hsderiv (t : ℝ) : HasDerivAt s (ds t) t := by
      convert (stackFundamentalSolution_hasDerivAt k hlayers x (x + t)).scomp t
        ((hasDerivAt_id t).const_add x) using 1 <;> simp [s, ds, v, Function.comp_def]
    have hdsderiv (t : ℝ) (_ht : t ∈ Ioo 0 h) (htbad : t ∉ bad) :
        HasDerivAt ds (-(k : ℂ) ^ 2 * ((p t : ℂ) + Complex.I * (q t : ℂ)) * s t) t := by
      have hiface : x + t ∉ interfacePositions layers := by
        intro hz
        apply htbad
        exact Finset.mem_image.mpr ⟨x + t, List.mem_toFinset.mpr hz, by ring⟩
      have hd := (stackMagneticField_maxwell_offInterfaces k hlayers v (x + t) hiface).scomp t
        ((hasDerivAt_id t).const_add x)
      have hscaled := hd.const_mul (Complex.I * (k : ℂ))
      convert hscaled using 1
      · rfl
      · dsimp [ds, s, p, q, stackFundamentalSolution, v]
        ring_nf
        simp [Complex.I_sq]
        ring
    have hcap (t : ℝ) (ht : t ∈ Ioo 0 h) : k ^ 2 * p t ≤ (k * Real.sqrt P) ^ 2 := by
      have hp := hlocal (x + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg k)
      simpa only [mul_pow, Real.sq_sqrt hP.le] using hm
    have hs0 : s 0 = 0 := by
      simpa [s] using stackFundamentalSolution_initial k hlayers x
    have hds0 : ds 0 = 1 := by
      have hi := congrFun (stackFundamentalState_initial k hlayers x) 1
      have hkn : Complex.I * (k : ℂ) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk.ne')
      dsimp [ds]
      simp only [add_zero]
      change Complex.I * (k : ℂ) *
        partialState k layers (stackFundamentalState k layers x) x 1 = 1
      rw [hi]
      change (Complex.I * (k : ℂ)) * (Complex.I * (k : ℂ))⁻¹ = 1
      exact mul_inv_cancel₀ hkn
    exact ModulusComparison.helmholtz_modulus_comparison hK hh hKh bad hscont hdscont
      hsderiv hdsderiv hcap hs0 hds0

#print axioms stackFundamentalSolution_modulus_comparison

/-- The same comparison for the finite physical class, without prescribed exterior caps. -/
theorem finitePhysicalStack_modulus_comparison {k P x h : ℝ}
    (hk : 0 < k) (hP : 0 < P) {layers : List HomogeneousLayer}
    (hlayers : FinitePhysicalStack layers)
    (hh : 0 ≤ h) (hmax : h ≤ Real.pi / (k * Real.sqrt P))
    (hlocal : ∀ z ∈ Ioo x (x + h), stackRealProfile layers z ≤ P) :
    Real.sin (k * Real.sqrt P * h) / (k * Real.sqrt P) ≤
      ‖stackFundamentalSolution k layers (x + h) x‖ := by
  obtain ⟨Pglobal, Qglobal, _, _, hc⟩ := finitePhysicalStack_exists_caps hlayers
  exact stackFundamentalSolution_modulus_comparison hk hP hc hh hmax hlocal

#print axioms finitePhysicalStack_modulus_comparison
end OQ7
