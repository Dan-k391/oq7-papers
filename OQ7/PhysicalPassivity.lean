import OQ7.Scattering
import OQ7.Fields
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace OQ7

open scoped ComplexOrder Matrix

/-- Twice the directed flux is the actual field-state quadratic form. -/
theorem fluxForm_quadratic (u : Fin 2 → ℂ) :
    star u ⬝ᵥ (fluxForm *ᵥ u) = ((2 * directedFlux (u 0) (u 1) : ℝ) : ℂ) := by
  simp [fluxForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  apply Complex.ext <;>
    simp [directedFlux, Complex.mul_re, Complex.mul_im] <;> ring

theorem fluxDefect_quadratic (F : Mat2) (u : Fin 2 → ℂ) :
    star u ⬝ᵥ (fluxDefect F *ᵥ u) =
      ((2 * (directedFlux (u 0) (u 1) -
        directedFlux ((F *ᵥ u) 0) ((F *ᵥ u) 1)) : ℝ) : ℂ) := by
  have hcore : star u ⬝ᵥ ((F.conjTranspose * fluxForm * F) *ᵥ u) =
      star (F *ᵥ u) ⬝ᵥ (fluxForm *ᵥ (F *ᵥ u)) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec, Matrix.vecMul_vecMul]
  simp only [fluxDefect, Matrix.sub_mulVec, dotProduct_sub, hcore,
    fluxForm_quadratic]
  push_cast
  ring

/-- The flux of every actual homogeneous Maxwell field decreases through passive material. -/
theorem layerDirectedFlux_antitone {k : ℝ} (hk : 0 ≤ k) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (hq : 0 ≤ layer.q) (E₀ H₀ : ℂ) :
    Antitone (fun x => directedFlux (layerElectricField k layer E₀ H₀ x)
      (layerMagneticField k layer E₀ H₀ x)) := by
  apply antitone_of_hasDerivAt_nonpos (fun z => layerDirectedFlux_hasDerivAt k hp E₀ H₀ z)
  intro z
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) hq)
    (Complex.normSq_nonneg _)

/-- Positive semidefinite field defect, derived from Maxwell's flux law for an actual layer. -/
theorem layerTransfer_fluxDefect_posSemidef {k : ℝ} (hk : 0 ≤ k)
    {layer : HomogeneousLayer} (hp : 1 ≤ layer.p) (hq : 0 ≤ layer.q)
    (hw : 0 ≤ layer.width) : (fluxDefect (layerTransfer k layer)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact fluxDefect_conjTranspose _
  · intro u
    have hflux := layerDirectedFlux_antitone hk hp hq (u 0) (u 1) hw
    have hzero := homogeneousField_initial k (refractiveIndex layer) (u 0) (u 1)
    change directedFlux (layerElectricField k layer (u 0) (u 1) layer.width)
        (layerMagneticField k layer (u 0) (u 1) layer.width) ≤
      directedFlux (electricField k (refractiveIndex layer) (u 0) (u 1) 0)
        (magneticField k (refractiveIndex layer) (u 0) (u 1) 0) at hflux
    rw [hzero.1, hzero.2] at hflux
    have hu : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
    have hboundary := layerField_transfer_boundary k layer (u 0) (u 1)
    rw [← hu] at hboundary
    rw [fluxDefect_quadratic, hboundary]
    apply RCLike.nonneg_iff.mpr
    constructor
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr hflux)
    · simp

/-- Flux defects add with the exact congruence required by composition of physical transfers. -/
theorem fluxDefect_mul (B A : Mat2) :
    fluxDefect (B * A) = fluxDefect A + A.conjTranspose * fluxDefect B * A := by
  unfold fluxDefect
  simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

theorem fluxDefect_mul_posSemidef (B A : Mat2)
    (hB : (fluxDefect B).PosSemidef) (hA : (fluxDefect A).PosSemidef) :
    (fluxDefect (B * A)).PosSemidef := by
  rw [fluxDefect_mul]
  exact hA.add (hB.conjTranspose_mul_mul_same A)

theorem stackTransfer_fluxDefect_posSemidef {k P Q : ℝ} (hk : 0 ≤ k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    (fluxDefect (stackTransfer k layers)).PosSemidef := by
  induction layers with
  | nil => simpa [stackTransfer, fluxDefect] using (Matrix.PosSemidef.zero : (0 : Mat2).PosSemidef)
  | cons layer layers ih =>
      have hl := h layer (by simp)
      have ht : StackAdmissible P Q layers := by
        intro other hm
        exact h other (by simp [hm])
      rw [stackTransfer]
      exact fluxDefect_mul_posSemidef _ _ (ih ht)
        (layerTransfer_fluxDefect_posSemidef hk hl.1 hl.2.2.1 hl.2.2.2.2)

/-- Every finite admissible physical stack has a well-defined scattering denominator. -/
theorem stackTransfer_denominator_ne_zero {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    waveTransfer (stackTransfer k layers) 1 1 ≠ 0 := by
  exact passive_transfer_denominator_ne_zero _ (stackTransfer_fluxDefect_posSemidef hk.le h)

/-- Passivity of the actual scattering matrix of every finite admissible physical stack. -/
theorem stack_scattering_passive {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    Passive (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferReflectionRight (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) := by
  exact passive_transfer_scattering _ (stackTransfer_fluxDefect_posSemidef hk.le h)
    (stackTransfer_det k h)

theorem stack_transmission_ne_zero {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    transferTransmissionRight (waveTransfer (stackTransfer k layers)) ≠ 0 := by
  exact passive_transfer_transmission_ne_zero _ (stackTransfer_fluxDefect_posSemidef hk.le h)

theorem stack_absorption_det_ratio {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
        (transferReflectionRight (waveTransfer (stackTransfer k layers)))
        (transferTransmissionRight (waveTransfer (stackTransfer k layers)))).det /
      (Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) : ℂ) =
        (fluxDefect (stackTransfer k layers)).det := by
  exact passive_transfer_absorption_det_ratio _ (stackTransfer_fluxDefect_posSemidef hk.le h)
    (stackTransfer_det k h)

#print axioms fluxForm_quadratic
#print axioms fluxDefect_quadratic
#print axioms layerDirectedFlux_antitone
#print axioms layerTransfer_fluxDefect_posSemidef
#print axioms fluxDefect_mul
#print axioms fluxDefect_mul_posSemidef
#print axioms stackTransfer_fluxDefect_posSemidef
#print axioms stackTransfer_denominator_ne_zero
#print axioms stack_scattering_passive
#print axioms stack_transmission_ne_zero
#print axioms stack_absorption_det_ratio

end OQ7
