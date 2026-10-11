import OQ7.PhysicalPassivity
import OQ7.Passivity
import OQ7.Target
noncomputable section
namespace OQ7
open scoped ComplexOrder Matrix Topology
open Filter


theorem layerDirectedFlux_strict {k : ℝ} (hk : 0 < k) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (hq : 0 < layer.q) (hw : 0 < layer.width) (E₀ H₀ : ℂ)
    (hinput : (![E₀, H₀] : Fin 2 → ℂ) ≠ 0) :
    directedFlux (layerElectricField k layer E₀ H₀ layer.width)
      (layerMagneticField k layer E₀ H₀ layer.width) < directedFlux E₀ H₀ := by
  let f := fun x => directedFlux (layerElectricField k layer E₀ H₀ x)
    (layerMagneticField k layer E₀ H₀ x)
  have hf : Antitone f := layerDirectedFlux_antitone hk.le hp hq.le E₀ H₀
  have hzero : f 0 = directedFlux E₀ H₀ := by
    simp [f, layerElectricField, layerMagneticField, electricField, magneticField]
  change f layer.width < directedFlux E₀ H₀
  rw [← hzero]
  apply lt_of_le_of_ne (hf hw.le)
  intro heq
  have hElectricZero : ∀ x ∈ Set.Ioo 0 layer.width,
      layerElectricField k layer E₀ H₀ x = 0 := by
    intro x hx
    have hevent : f =ᶠ[𝓝 x] (fun _ => f 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      apply le_antisymm (hf hy.1.le)
      rw [← heq]
      exact hf hy.2.le
    have hc := (hasDerivAt_const x (f 0)).congr_of_eventuallyEq hevent
    have hz := (layerDirectedFlux_hasDerivAt k hp E₀ H₀ x).unique hc
    have hnorm : Complex.normSq (layerElectricField k layer E₀ H₀ x) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (neg_ne_zero.mpr hk.ne') hq.ne')
    exact Complex.normSq_eq_zero.mp hnorm
  let x := layer.width / 2
  have hx : x ∈ Set.Ioo 0 layer.width := by dsimp [x]; constructor <;> linarith
  have heventE : layerElectricField k layer E₀ H₀ =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hElectricZero y hy
  have hcE := (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq heventE
  have hzH := (layerElectricField_maxwell k hp E₀ H₀ x).unique hcE
  have hkn : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hHzero : layerMagneticField k layer E₀ H₀ x = 0 := by
    exact (mul_eq_zero.mp hzH).resolve_left (mul_ne_zero Complex.I_ne_zero hkn)
  have hstate : homogeneousTransfer k (refractiveIndex layer) x *ᵥ ![E₀, H₀] = 0 := by
    rw [homogeneousField_transfer]
    change ![layerElectricField k layer E₀ H₀ x, layerMagneticField k layer E₀ H₀ x] = 0
    rw [hElectricZero x hx, hHzero]
    ext i
    fin_cases i <;> rfl
  have hdet : (homogeneousTransfer k (refractiveIndex layer) x).det ≠ 0 := by
    rw [homogeneousTransfer_det k (refractiveIndex_ne_zero hp) x]
    norm_num
  exact hinput (Matrix.eq_zero_of_mulVec_eq_zero hdet hstate)

/-- Every positive-width homogeneous lossy dielectric has a positive-definite flux defect. -/
theorem layerTransfer_fluxDefect_posDef {k : ℝ} (hk : 0 < k)
    {layer : HomogeneousLayer} (hp : 1 ≤ layer.p) (hq : 0 < layer.q)
    (hw : 0 < layer.width) : (fluxDefect (layerTransfer k layer)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact fluxDefect_conjTranspose _
  · intro u hu
    have hvec : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
    have hinput : (![u 0, u 1] : Fin 2 → ℂ) ≠ 0 := by rw [← hvec]; exact hu
    have hflux := layerDirectedFlux_strict hk hp hq hw (u 0) (u 1) hinput
    have hboundary := layerField_transfer_boundary k layer (u 0) (u 1)
    rw [← hvec] at hboundary
    rw [fluxDefect_quadratic, hboundary]
    apply RCLike.pos_iff.mpr
    constructor
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact mul_pos (by norm_num) (sub_pos.mpr hflux)
    · simp

/-- Any positive integrated loss in a finite admissible physical stack gives a positive defect. -/
theorem stackTransfer_fluxDefect_posDef {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers)
    (hM : 0 < integratedLoss layers) : (fluxDefect (stackTransfer k layers)).PosDef := by
  induction layers with
  | nil => simp [integratedLoss] at hM
  | cons layer layers ih =>
      have hl := h layer (by simp)
      have ht : StackAdmissible P Q layers := by
        intro other hm
        exact h other (by simp [hm])
      rw [stackTransfer, fluxDefect_mul]
      by_cases hprod : 0 < layer.q * layer.width
      · have hq : 0 < layer.q := by
          by_contra hz
          have hq0 : layer.q = 0 := le_antisymm (le_of_not_gt hz) hl.2.2.1
          simp [hq0] at hprod
        have hw : 0 < layer.width := by
          by_contra hz
          have hw0 : layer.width = 0 := le_antisymm (le_of_not_gt hz) hl.2.2.2.2
          simp [hw0] at hprod
        exact (layerTransfer_fluxDefect_posDef hk hl.1 hq hw).add_posSemidef
          ((stackTransfer_fluxDefect_posSemidef hk.le ht).conjTranspose_mul_mul_same _)
      · have htail : 0 < integratedLoss layers := by
          simp only [integratedLoss, List.map_cons, List.sum_cons] at hM ⊢
          have hn := le_of_not_gt hprod
          linarith
        have hinj : Function.Injective (layerTransfer k layer).mulVec := by
          apply Matrix.mulVec_injective_of_det_ne_zero
          rw [layerTransfer_det k hl]
          norm_num
        exact Matrix.PosDef.posSemidef_add
          (layerTransfer_fluxDefect_posSemidef hk.le hl.1 hl.2.2.1 hl.2.2.2.2)
          ((ih ht htail).conjTranspose_mul_mul_same hinj)

/-- Positive physical loss rules out a lossless coherent input for the actual scattering matrix. -/
theorem stack_absorption_posDef {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers)
    (hM : 0 < integratedLoss layers) :
    (absorptionMatrix (stackReflectionLeft k layers) (stackReflectionRight k layers)
      (stackTransmission k layers)).PosDef := by
  have hD := stackTransfer_fluxDefect_posDef hk h hM
  have ht := stack_transmission_ne_zero hk h
  have hd := stackTransfer_denominator_ne_zero hk h
  have hdet := stackTransfer_det k h
  have hinj : Function.Injective
      (inputFieldStates (stackReflectionLeft k layers) (stackTransmission k layers)).mulVec := by
    apply Matrix.mulVec_injective_of_det_ne_zero
    rw [inputFieldStates_det]
    exact mul_ne_zero (by norm_num) ht
  have hcong := hD.conjTranspose_mul_mul_same hinj
  change ((inputFieldStates (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers)))).conjTranspose *
    fluxDefect (stackTransfer k layers) *
    inputFieldStates (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers)))).PosDef at hcong
  rw [← transfer_absorption_fluxDefect _ hd hdet] at hcong
  have hscaled := hcong.smul (show (0 : ℂ) < 1 / 2 by rw [RCLike.pos_iff]; norm_num)
  simpa [smul_smul, stackReflectionLeft, stackReflectionRight, stackTransmission] using hscaled

theorem stack_absorption_det_pos {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers)
    (hM : 0 < integratedLoss layers) :
    0 < (absorptionMatrix (stackReflectionLeft k layers) (stackReflectionRight k layers)
      (stackTransmission k layers)).det.re := by
  exact (Complex.pos_iff.mp (stack_absorption_posDef hk h hM).det_pos).1

/-- The strict finite-stack inequality asserted in Theorem 5.1, with its exact physical targets. -/
theorem exactTargetClass_strict_gap {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    stackAsymmetry p.k layers < ScalarEnvelope.D0 p.T p.a := by
  have hp := stack_scattering_passive p.k_pos hm.1
  have ht := hm.2.2.2.1
  have ha := hm.2.2.2.2
  have hM : 0 < integratedLoss layers := by rw [hm.2.1]; exact p.M_pos
  have hd := stack_absorption_det_pos p.k_pos hm.1 hM
  have hactive : ScalarEnvelope.ActiveTarget (stackTransmissionPower p.k layers)
      (stackMeanAbsorptance p.k layers) := by
    rw [ht, ha]
    exact p.active
  have hb := active_matrix_strict_gap hp hactive hd
  change stackAsymmetry p.k layers <
    ScalarEnvelope.D0 (stackTransmissionPower p.k layers) (stackMeanAbsorptance p.k layers) at hb
  simpa only [ht, ha] using hb

#print axioms layerDirectedFlux_strict
#print axioms layerTransfer_fluxDefect_posDef
#print axioms stackTransfer_fluxDefect_posDef
#print axioms stack_absorption_posDef
#print axioms stack_absorption_det_pos
#print axioms exactTargetClass_strict_gap
end OQ7


