import OQ7.PhysicalGlobal
import OQ7.Gram

noncomputable section

namespace OQ7

open scoped Matrix

/-- Actual left-boundary states of the two unit-incidence scattering solutions. -/
def stackInputMatrix (k : ℝ) (layers : List HomogeneousLayer) : Mat2 :=
  inputFieldStates (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
    (transferTransmissionRight (waveTransfer (stackTransfer k layers)))

def stackScatteringStates (k : ℝ) (layers : List HomogeneousLayer) (z : ℝ) : Mat2 :=
  partialTransfer k layers z * stackInputMatrix k layers

def stackScatteringElectric (k : ℝ) (layers : List HomogeneousLayer)
    (port : Fin 2) (z : ℝ) : ℂ := stackScatteringStates k layers z 0 port

def stackScatteringMagnetic (k : ℝ) (layers : List HomogeneousLayer)
    (port : Fin 2) (z : ℝ) : ℂ := stackScatteringStates k layers z 1 port

/-- Propagate the physical state `(E,H)=(0,1/(ik))` back to the left boundary. -/
def stackFundamentalState (k : ℝ) (layers : List HomogeneousLayer)
    (x : ℝ) : Fin 2 → ℂ :=
  adjugate2 (partialTransfer k layers x) *ᵥ ![0, (Complex.I * (k : ℂ))⁻¹]

/-- The exact finite-layer solution with electric initial data `s(x)=0`, `s'(x)=1`. -/
def stackFundamentalSolution (k : ℝ) (layers : List HomogeneousLayer)
    (y x : ℝ) : ℂ := stackElectricField k layers (stackFundamentalState k layers x) y

theorem stackScatteringElectric_as_field (k : ℝ) (layers : List HomogeneousLayer)
    (port : Fin 2) :
    stackScatteringElectric k layers port =
      stackElectricField k layers (fun i => stackInputMatrix k layers i port) := by
  rfl

theorem stackScatteringMagnetic_as_field (k : ℝ) (layers : List HomogeneousLayer)
    (port : Fin 2) :
    stackScatteringMagnetic k layers port =
      stackMagneticField k layers (fun i => stackInputMatrix k layers i port) := by
  rfl

theorem stackScatteringElectric_hasDerivAt (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers)
    (port : Fin 2) (z : ℝ) :
    HasDerivAt (stackScatteringElectric k layers port)
      (Complex.I * (k : ℂ) * stackScatteringMagnetic k layers port z) z := by
  rw [stackScatteringElectric_as_field, stackScatteringMagnetic_as_field]
  exact stackElectricField_maxwell k h _ z

theorem stackScatteringStates_det (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (z : ℝ) :
    (stackScatteringStates k layers z).det =
      -2 * transferTransmissionRight (waveTransfer (stackTransfer k layers)) := by
  simp [stackScatteringStates, Matrix.det_mul, partialTransfer_det k h,
    stackInputMatrix, inputFieldStates_det]

theorem stackFundamentalState_initial (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x : ℝ) :
    partialState k layers (stackFundamentalState k layers x) x =
      ![0, (Complex.I * (k : ℂ))⁻¹] := by
  simp only [partialState, stackFundamentalState, Matrix.mulVec_mulVec,
    mul_adjugate2, partialTransfer_det k h, one_smul, Matrix.one_mulVec]

theorem stackFundamentalSolution_initial (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x : ℝ) :
    stackFundamentalSolution k layers x x = 0 := by
  have hi := congrFun (stackFundamentalState_initial k h x) 0
  exact hi

theorem stackFundamentalSolution_hasDerivAt (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x y : ℝ) :
    HasDerivAt (fun y => stackFundamentalSolution k layers y x)
      (Complex.I * (k : ℂ) * stackMagneticField k layers
        (stackFundamentalState k layers x) y) y := by
  exact stackElectricField_maxwell k h _ y

theorem stackFundamentalSolution_deriv_initial {k : ℝ} (hk : k ≠ 0) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x : ℝ) :
    HasDerivAt (fun y => stackFundamentalSolution k layers y x) 1 x := by
  have hd := stackFundamentalSolution_hasDerivAt k h x x
  have hi := congrFun (stackFundamentalState_initial k h x) 1
  change stackMagneticField k layers (stackFundamentalState k layers x) x =
    (Complex.I * (k : ℂ))⁻¹ at hi
  rw [hi] at hd
  have hc : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (by exact_mod_cast hk)
  rw [mul_inv_cancel₀ hc] at hd
  exact hd

theorem stackFundamentalSolution_transferFormula (k : ℝ)
    (layers : List HomogeneousLayer) (y x : ℝ) :
    stackFundamentalSolution k layers y x =
      (partialTransfer k layers y * adjugate2 (partialTransfer k layers x)) 0 1 /
        (Complex.I * (k : ℂ)) := by
  simp [stackFundamentalSolution, stackElectricField, partialState, stackFundamentalState,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  ring

theorem stackFundamentalSolution_continuous (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x : ℝ) :
    Continuous (fun y => stackFundamentalSolution k layers y x) := by
  exact stackElectricField_continuous k h _

theorem stackFundamentalDerivative_continuous (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x : ℝ) :
    Continuous (deriv (fun y => stackFundamentalSolution k layers y x)) := by
  have hfirst : deriv (fun y => stackFundamentalSolution k layers y x) =
      fun y => Complex.I * (k : ℂ) *
        stackMagneticField k layers (stackFundamentalState k layers x) y := by
    funext y
    exact (stackFundamentalSolution_hasDerivAt k h x y).deriv
  rw [hfirst]
  exact (stackMagneticField_continuous k h _).const_mul _

/-- The fundamental solution satisfies the original complex Helmholtz equation inside every layer. -/
theorem stackFundamentalSolution_helmholtz_offInterfaces (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (x y : ℝ)
    (hy : y ∉ interfacePositions layers) :
    deriv (deriv (fun y => stackFundamentalSolution k layers y x)) y +
      (k : ℂ) ^ 2 * ((stackRealProfile layers y : ℂ) +
        Complex.I * (stackLossProfile layers y : ℂ)) *
          stackFundamentalSolution k layers y x = 0 := by
  have hfirst : deriv (fun y => stackFundamentalSolution k layers y x) =
      fun y => Complex.I * (k : ℂ) *
        stackMagneticField k layers (stackFundamentalState k layers x) y := by
    funext y
    exact (stackFundamentalSolution_hasDerivAt k h x y).deriv
  rw [hfirst]
  rw [((stackMagneticField_maxwell_offInterfaces k h (stackFundamentalState k layers x)
    y hy).const_mul (Complex.I * (k : ℂ))).deriv]
  change (Complex.I * (k : ℂ)) * (Complex.I * (k : ℂ) *
    ((stackRealProfile layers y : ℂ) + Complex.I * (stackLossProfile layers y : ℂ)) *
      stackFundamentalSolution k layers y x) + _ = 0
  ring_nf
  simp [Complex.I_sq]

theorem stackScatteringWronskian (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) (z : ℝ) :
    stackScatteringElectric k layers 0 z * deriv (stackScatteringElectric k layers 1) z -
      deriv (stackScatteringElectric k layers 0) z * stackScatteringElectric k layers 1 z =
        -2 * Complex.I * (k : ℂ) *
          transferTransmissionRight (waveTransfer (stackTransfer k layers)) := by
  rw [(stackScatteringElectric_hasDerivAt k h 0 z).deriv,
    (stackScatteringElectric_hasDerivAt k h 1 z).deriv]
  have hdet := stackScatteringStates_det k h z
  rw [Matrix.det_fin_two] at hdet
  change stackScatteringElectric k layers 0 z * stackScatteringMagnetic k layers 1 z -
    stackScatteringElectric k layers 1 z * stackScatteringMagnetic k layers 0 z = _ at hdet
  calc
    _ = Complex.I * (k : ℂ) *
        (stackScatteringElectric k layers 0 z * stackScatteringMagnetic k layers 1 z -
          stackScatteringElectric k layers 1 z * stackScatteringMagnetic k layers 0 z) := by ring
    _ = _ := by rw [hdet]; ring

theorem stackScatteringWedge {k : ℝ} (hk : k ≠ 0)
    (layers : List HomogeneousLayer) (x y : ℝ) :
    stackScatteringElectric k layers 0 x * stackScatteringElectric k layers 1 y -
      stackScatteringElectric k layers 1 x * stackScatteringElectric k layers 0 y =
        -2 * Complex.I * (k : ℂ) *
          transferTransmissionRight (waveTransfer (stackTransfer k layers)) *
            stackFundamentalSolution k layers y x := by
  change (partialTransfer k layers x * stackInputMatrix k layers) 0 0 *
      (partialTransfer k layers y * stackInputMatrix k layers) 0 1 -
    (partialTransfer k layers x * stackInputMatrix k layers) 0 1 *
      (partialTransfer k layers y * stackInputMatrix k layers) 0 0 = _
  rw [matrixElectricWedge]
  simp only [stackInputMatrix, inputFieldStates_det]
  rw [stackFundamentalSolution_transferFormula]
  have hc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  field_simp

theorem stackScatteringWedge_normSq {k : ℝ} (hk : k ≠ 0)
    (layers : List HomogeneousLayer) (x y : ℝ) :
    Complex.normSq
      (stackScatteringElectric k layers 0 x * stackScatteringElectric k layers 1 y -
        stackScatteringElectric k layers 1 x * stackScatteringElectric k layers 0 y) =
      4 * k ^ 2 * Complex.normSq
        (transferTransmissionRight (waveTransfer (stackTransfer k layers))) *
          Complex.normSq (stackFundamentalSolution k layers y x) := by
  rw [stackScatteringWedge hk]
  have htwo : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal,
    Complex.normSq_I, htwo]
  ring

def stackFundamentalPairKernel (k : ℝ) (layers : List HomogeneousLayer)
    (p : ℝ × ℝ) : ℝ :=
  stackLossProfile layers p.1 * stackLossProfile layers p.2 *
    Complex.normSq (stackFundamentalSolution k layers p.2 p.1)

theorem stackScatteringGramPairKernel {k : ℝ} (hk : k ≠ 0)
    (layers : List HomogeneousLayer) (p : ℝ × ℝ) :
    gramPairKernel (stackLossProfile layers)
      (fun z port => stackScatteringElectric k layers port z) p =
      (4 * k ^ 2 * Complex.normSq
        (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) *
          stackFundamentalPairKernel k layers p := by
  unfold gramPairKernel stackFundamentalPairKernel
  rw [stackScatteringWedge_normSq hk]
  ring

#print axioms stackScatteringElectric_as_field
#print axioms stackScatteringMagnetic_as_field
#print axioms stackScatteringElectric_hasDerivAt
#print axioms stackScatteringStates_det
#print axioms stackFundamentalState_initial
#print axioms stackFundamentalSolution_initial
#print axioms stackFundamentalSolution_hasDerivAt
#print axioms stackFundamentalSolution_deriv_initial
#print axioms stackFundamentalSolution_transferFormula
#print axioms stackFundamentalSolution_continuous
#print axioms stackFundamentalDerivative_continuous
#print axioms stackFundamentalSolution_helmholtz_offInterfaces
#print axioms stackScatteringWronskian
#print axioms stackScatteringWedge
#print axioms stackScatteringWedge_normSq
#print axioms stackScatteringGramPairKernel

end OQ7
