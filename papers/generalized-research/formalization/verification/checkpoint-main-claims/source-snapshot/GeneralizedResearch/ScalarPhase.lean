import OQ7.SharpPhysicalConstruction
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-! Actual lossless reflectionless slabs tune the vacuum-reference transmission
phase with bounded added thickness. A vacuum spacer alone cannot do this.
Every slab below is a literal HomogeneousLayer and its transfer and fields are
proved from the homogeneous Helmholtz solutions. -/
noncomputable section
namespace GeneralizedResearch
namespace ScalarPhase
open OQ7
open scoped Matrix

def periodAngle (N : ℕ) : ℝ := 2 * (N : ℝ) * Real.pi
def phaseIndex (N : ℕ) (φ : ℝ) : ℝ := periodAngle N / (periodAngle N - φ)
def phaseWidth (k : ℝ) (N : ℕ) (φ : ℝ) : ℝ := (periodAngle N - φ) / k
def phaseLayer (k : ℝ) (N : ℕ) (φ : ℝ) : HomogeneousLayer :=
  ⟨phaseIndex N φ ^ 2, 0, phaseWidth k N φ⟩
def referenceTransmission (k : ℝ) (layers : List HomogeneousLayer) : ℂ :=
  Complex.exp (-((k * totalThickness layers : ℝ) : ℂ) * Complex.I) * stackTransmission k layers
def compensatingAngle (z : ℂ) : ℝ := 2 * Real.pi - z.arg

theorem exists_phase_count {P : ℝ} (hP : 1 < P) :
    ∃ N : ℕ, 1 ≤ N ∧ 4 * Real.pi <
      periodAngle N * (Real.sqrt P - 1) / Real.sqrt P := by
  have hP0 : 0 ≤ P := by linarith
  have hr2 := Real.sq_sqrt hP0
  have hr0 := Real.sqrt_nonneg P
  have hr : 1 < Real.sqrt P := by nlinarith
  have hgap : 0 < (Real.sqrt P - 1) / Real.sqrt P := div_pos (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 / ((Real.sqrt P - 1) / Real.sqrt P)))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNgap : 2 < (N : ℝ) * ((Real.sqrt P - 1) / Real.sqrt P) :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hN)
  refine ⟨N, by exact_mod_cast hN1.le, ?_⟩
  unfold periodAngle
  have hmul := mul_lt_mul_of_pos_right hNgap (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  convert hmul using 1 <;> ring

theorem phase_properties {k P φ : ℝ} {N : ℕ} (hk : 0 < k) (hP : 1 < P) (hN : 1 ≤ N)
    (hcover : 4 * Real.pi < periodAngle N * (Real.sqrt P - 1) / Real.sqrt P)
    (hφ0 : 0 ≤ φ) (hφ4 : φ ≤ 4 * Real.pi) :
    1 ≤ phaseIndex N φ ∧ phaseIndex N φ ^ 2 ≤ P ∧
    0 < phaseWidth k N φ ∧ phaseWidth k N φ ≤ periodAngle N / k ∧
    k * phaseIndex N φ * phaseWidth k N φ = periodAngle N := by
  have hP0 : 0 ≤ P := by linarith
  have hr2 := Real.sq_sqrt hP0
  have hr0 := Real.sqrt_nonneg P
  have hr : 1 < Real.sqrt P := by nlinarith
  have hA : 0 < periodAngle N := by
    unfold periodAngle
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hcover' := (lt_div_iff₀ (by linarith : 0 < Real.sqrt P)).mp hcover
  have hφr : φ * Real.sqrt P ≤ (4 * Real.pi) * Real.sqrt P :=
    mul_le_mul_of_nonneg_right hφ4 hr0
  have hden : 0 < periodAngle N - φ := by nlinarith
  have hn1 : 1 ≤ phaseIndex N φ := by
    unfold phaseIndex
    apply (one_le_div hden).mpr
    linarith
  have hnr : phaseIndex N φ ≤ Real.sqrt P := by
    unfold phaseIndex
    apply (div_le_iff₀ hden).mpr
    nlinarith
  refine ⟨hn1, by nlinarith, div_pos hden hk, ?_, ?_⟩
  · unfold phaseWidth
    exact (div_le_div_iff_of_pos_right hk).mpr (by linarith)
  · unfold phaseIndex phaseWidth
    field_simp [hk.ne', hden.ne']

theorem phaseLayer_admissible {k P Q φ : ℝ} {N : ℕ} (hk : 0 < k) (hP : 1 < P)
    (hQ : 0 ≤ Q) (hN : 1 ≤ N)
    (hcover : 4 * Real.pi < periodAngle N * (Real.sqrt P - 1) / Real.sqrt P)
    (hφ0 : 0 ≤ φ) (hφ4 : φ ≤ 4 * Real.pi) : LayerAdmissible P Q (phaseLayer k N φ) := by
  have hp := phase_properties hk hP hN hcover hφ0 hφ4
  exact ⟨by dsimp [phaseLayer]; nlinarith [hp.1], hp.2.1, le_rfl, hQ, hp.2.2.1.le⟩

theorem phaseLayer_index {k φ : ℝ} {N : ℕ} (hn : 0 ≤ phaseIndex N φ) :
    refractiveIndex (phaseLayer k N φ) = (phaseIndex N φ : ℂ) := by
  unfold refractiveIndex relativePermittivity phaseLayer
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg (phaseIndex N φ))]
  simp only [Complex.ofReal_re, Real.sqrt_sq hn]

theorem homogeneous_period_transfer {k n width : ℝ} (N : ℕ)
    (hphase : k * n * width = periodAngle N) :
    homogeneousTransfer k (n : ℂ) width = 1 := by
  have hθ : (k : ℂ) * (n : ℂ) * (width : ℂ) = (N : ℂ) * (2 * (Real.pi : ℂ)) := by
    have hθ' := congrArg (fun x : ℝ => (x : ℂ)) hphase
    simpa only [Complex.ofReal_mul, periodAngle, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      mul_comm, mul_left_comm, mul_assoc] using hθ'
  have hs : Complex.sin ((N : ℂ) * (2 * (Real.pi : ℂ))) = 0 := by
    simpa using Complex.sin_nat_mul_two_pi_sub 0 N
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homogeneousTransfer, hθ, Complex.cos_nat_mul_two_pi, hs]

theorem phaseLayer_transfer {k P φ : ℝ} {N : ℕ} (hk : 0 < k) (hP : 1 < P) (hN : 1 ≤ N)
    (hcover : 4 * Real.pi < periodAngle N * (Real.sqrt P - 1) / Real.sqrt P)
    (hφ0 : 0 ≤ φ) (hφ4 : φ ≤ 4 * Real.pi) : layerTransfer k (phaseLayer k N φ) = 1 := by
  have hp := phase_properties hk hP hN hcover hφ0 hφ4
  rw [layerTransfer, phaseLayer_index (by linarith [hp.1])]
  exact homogeneous_period_transfer N hp.2.2.2.2

/-- The actual Helmholtz/Maxwell layer fields have the identical state at both
ends of the reflectionless slab; this is a derived transfer identity. -/
theorem phaseLayer_field_boundary {k P φ : ℝ} {N : ℕ} (hk : 0 < k) (hP : 1 < P) (hN : 1 ≤ N)
    (hcover : 4 * Real.pi < periodAngle N * (Real.sqrt P - 1) / Real.sqrt P)
    (hφ0 : 0 ≤ φ) (hφ4 : φ ≤ 4 * Real.pi) (E H : ℂ) :
    electricField k (phaseIndex N φ : ℂ) E H (phaseWidth k N φ) = E ∧
      magneticField k (phaseIndex N φ : ℂ) E H (phaseWidth k N φ) = H := by
  have hp := phase_properties hk hP hN hcover hφ0 hφ4
  have h := homogeneousField_transfer k (phaseIndex N φ : ℂ) E H (phaseWidth k N φ)
  rw [homogeneous_period_transfer N hp.2.2.2.2, Matrix.one_mulVec] at h
  exact ⟨(congrArg (fun v : Fin 2 → ℂ => v 0) h).symm,
    (congrArg (fun v : Fin 2 → ℂ => v 1) h).symm⟩

theorem period_exp (N : ℕ) : Complex.exp ((periodAngle N : ℂ) * Complex.I) = 1 := by
  have hθ : (periodAngle N : ℂ) = (N : ℂ) * (2 * (Real.pi : ℂ)) := by
    simp only [periodAngle, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    ring
  have hs : Complex.sin ((N : ℂ) * (2 * (Real.pi : ℂ))) = 0 := by
    simpa using Complex.sin_nat_mul_two_pi_sub 0 N
  rw [Complex.exp_mul_I, hθ, Complex.cos_nat_mul_two_pi, hs]
  simp

theorem phaseWidth_exp {k : ℝ} (hk : k ≠ 0) (N : ℕ) (φ : ℝ) :
    Complex.exp (-((k * phaseWidth k N φ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) := by
  have hw : k * phaseWidth k N φ = periodAngle N - φ := by
    unfold phaseWidth
    field_simp
  rw [hw, Complex.ofReal_sub]
  have heq : -((periodAngle N : ℂ) - (φ : ℂ)) * Complex.I =
      (φ : ℂ) * Complex.I - (periodAngle N : ℂ) * Complex.I := by ring
  rw [heq, Complex.exp_sub, period_exp, div_one]

theorem compensating_angle_properties (z : ℂ) :
    0 ≤ compensatingAngle z ∧ compensatingAngle z ≤ 4 * Real.pi ∧
    Complex.exp ((compensatingAngle z : ℝ) * Complex.I) * z = (‖z‖ : ℂ) := by
  have harg := Complex.arg_mem_Ioc z
  refine ⟨by unfold compensatingAngle; linarith [Real.pi_pos, harg.2],
    by unfold compensatingAngle; linarith [Real.pi_pos, harg.1], ?_⟩
  have heq : ((compensatingAngle z : ℝ) : ℂ) * Complex.I =
      (periodAngle 1 : ℂ) * Complex.I - (z.arg : ℂ) * Complex.I := by
    simp only [compensatingAngle, periodAngle, Nat.cast_one, mul_one, Complex.ofReal_sub]
    ring
  rw [heq, Complex.exp_sub, period_exp]
  calc
    _ = (1 / Complex.exp ((z.arg : ℂ) * Complex.I)) *
        ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = _ := by field_simp

theorem referenceTransmission_norm (k : ℝ) (layers : List HomogeneousLayer) :
    ‖referenceTransmission k layers‖ = ‖stackTransmission k layers‖ := by
  unfold referenceTransmission
  rw [norm_mul]
  have hn : ‖Complex.exp (-((k * totalThickness layers : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hn, one_mul]

theorem append_phase_transfer {k φ : ℝ} {N : ℕ} (layers : List HomogeneousLayer)
    (htransfer : layerTransfer k (phaseLayer k N φ) = 1) :
    stackTransfer k (layers ++ [phaseLayer k N φ]) = stackTransfer k layers := by
  rw [stackTransfer_append]
  simp only [stackTransfer, htransfer, one_mul]

theorem phaseLayer_thickness (k : ℝ) (N : ℕ) (φ : ℝ) :
    totalThickness [phaseLayer k N φ] = phaseWidth k N φ := by
  simp [totalThickness, phaseLayer]

theorem append_phase_reference {k φ : ℝ} {N : ℕ} (hk : k ≠ 0)
    (layers : List HomogeneousLayer) (htransfer : layerTransfer k (phaseLayer k N φ) = 1) :
    referenceTransmission k (layers ++ [phaseLayer k N φ]) =
      Complex.exp ((φ : ℂ) * Complex.I) * referenceTransmission k layers := by
  unfold referenceTransmission stackTransmission
  rw [append_phase_transfer layers htransfer, totalThickness_append]
  rw [phaseLayer_thickness]
  have heq : -((k * (totalThickness layers + phaseWidth k N φ) : ℝ) : ℂ) * Complex.I =
      -((k * totalThickness layers : ℝ) : ℂ) * Complex.I +
        -((k * phaseWidth k N φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [heq, Complex.exp_add, phaseWidth_exp hk]
  ring

def correctedStack (k : ℝ) (N : ℕ) (layers : List HomogeneousLayer) : List HomogeneousLayer :=
  layers ++ [phaseLayer k N (compensatingAngle (referenceTransmission k layers))]

/-- Actual bounded-thickness phase correction preserves every material/power
resource and makes the reference-normalized transmission real nonnegative. -/
theorem correction_properties {k P Q : ℝ} {N : ℕ} (hk : 0 < k) (hP : 1 < P)
    (hQ : 0 ≤ Q) (hN : 1 ≤ N)
    (hcover : 4 * Real.pi < periodAngle N * (Real.sqrt P - 1) / Real.sqrt P)
    (layers : List HomogeneousLayer) (hlayers : StackAdmissible P Q layers) :
    StackAdmissible P Q (correctedStack k N layers) ∧
    integratedLoss (correctedStack k N layers) = integratedLoss layers ∧
    stackTransmissionPower k (correctedStack k N layers) = stackTransmissionPower k layers ∧
    stackMeanAbsorptance k (correctedStack k N layers) = stackMeanAbsorptance k layers ∧
    stackAsymmetry k (correctedStack k N layers) = stackAsymmetry k layers ∧
    totalThickness (correctedStack k N layers) ≤ totalThickness layers + periodAngle N / k ∧
    referenceTransmission k (correctedStack k N layers) = (‖stackTransmission k layers‖ : ℂ) := by
  have ha := compensating_angle_properties (referenceTransmission k layers)
  have hp := phase_properties hk hP hN hcover ha.1 ha.2.1
  have hadm := phaseLayer_admissible hk hP hQ hN hcover ha.1 ha.2.1
  have ht := phaseLayer_transfer hk hP hN hcover ha.1 ha.2.1
  have hstack : stackTransfer k (correctedStack k N layers) = stackTransfer k layers :=
    append_phase_transfer layers ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro layer hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hlayers layer hmem
    · have heq : layer = phaseLayer k N (compensatingAngle (referenceTransmission k layers)) := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem
      exact heq ▸ hadm
  · rw [correctedStack, integratedLoss_append]
    simp [integratedLoss, phaseLayer]
  · unfold stackTransmissionPower stackTransmission
    rw [hstack]
  · unfold stackMeanAbsorptance stackReflectionLeft stackReflectionRight stackTransmission
    rw [hstack]
  · unfold stackAsymmetry stackReflectionLeft stackReflectionRight stackTransmission
    rw [hstack]
  · rw [correctedStack, totalThickness_append]
    rw [phaseLayer_thickness]
    linarith [hp.2.2.2.1]
  · rw [correctedStack, append_phase_reference hk.ne' layers ht, ha.2.2,
      referenceTransmission_norm]

end ScalarPhase
end GeneralizedResearch
