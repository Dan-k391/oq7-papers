import GeneralizedResearch.HelmholtzProfile

/-! Nonvacuous examples and exact embedding of the unchanged finite-layer
model. The broader profile model admits zero and negative real permittivity;
none of its resource inequalities is encoded as a model assumption. -/

noncomputable section
namespace GeneralizedResearch.HelmholtzProfile
open OQ7
open scoped Matrix

theorem basis_mulVec (A:Mat2) (j:Fin 2) :
    A*ᵥ(fun i=>(1:Mat2) i j)=fun i=>A i j := by
  ext i
  change (A*1) i j=A i j
  rw [mul_one]

def fromStack (k : ℝ) {P Q : ℝ} (hQ:0≤Q) (layers:List HomogeneousLayer)
    (h:StackAdmissible P Q layers) : Profile k where
  p := stackRealProfile layers
  q := stackLossProfile layers
  interfaces := (interfacePositions layers).toFinset
  field := partialTransfer k layers
  continuous i j := (continuous_apply j).comp ((continuous_apply i).comp (partialTransfer_continuous k h))
  initial := partialTransfer_zero k h
  electric_derivative j x := by
    have he : stackElectricField k layers (fun i=>(1:Mat2) i j)=fun z=>partialTransfer k layers z 0 j := by
      funext z
      exact congrFun (basis_mulVec (partialTransfer k layers z) j) 0
    have hm : stackMagneticField k layers (fun i=>(1:Mat2) i j)=fun z=>partialTransfer k layers z 1 j := by
      funext z
      exact congrFun (basis_mulVec (partialTransfer k layers z) j) 1
    simpa only [he,hm] using stackElectricField_maxwell k h (fun i=>(1:Mat2) i j) x
  magnetic_derivative j x hx := by
    have he : stackElectricField k layers (fun i=>(1:Mat2) i j)=fun z=>partialTransfer k layers z 0 j := by
      funext z
      exact congrFun (basis_mulVec (partialTransfer k layers z) j) 0
    have hm : stackMagneticField k layers (fun i=>(1:Mat2) i j)=fun z=>partialTransfer k layers z 1 j := by
      funext z
      exact congrFun (basis_mulVec (partialTransfer k layers z) j) 1
    simpa only [he,hm] using stackMagneticField_maxwell_offInterfaces k h (fun i=>(1:Mat2) i j) x
      (by simpa using hx)
  loss_integrable a b := stackLossProfile_intervalIntegrable a b hQ h
  passive x := (stackLossProfile_bounds hQ h x).1

theorem fromStack_transfer (k : ℝ) {P Q : ℝ} (hQ:0≤Q) (layers:List HomogeneousLayer)
    (h:StackAdmissible P Q layers) :
    (fromStack k hQ layers h).field (totalThickness layers)=stackTransfer k layers :=
  partialTransfer_total k h

theorem fromStack_invariant (k : ℝ) {P Q : ℝ} (hQ:0≤Q) (layers:List HomogeneousLayer)
    (h:StackAdmissible P Q layers) :
    (fromStack k hQ layers h).invariant (totalThickness layers)=(fluxDefect (stackTransfer k layers)).det.re := by
  rw [Profile.invariant,fromStack_transfer]

def zeroField (k x:ℝ) : Mat2 := !![1,Complex.I*(k:ℂ)*(x:ℂ);0,1]
def zeroProfile (k:ℝ) : Profile k where
  p := fun _=>0
  q := fun _=>0
  interfaces := ∅
  field := zeroField k
  continuous i j := by fin_cases i <;> fin_cases j <;> simp [zeroField] <;> fun_prop
  initial := by ext i j;fin_cases i <;> fin_cases j <;> simp [zeroField]
  electric_derivative j x := by
    fin_cases j
    · simpa [zeroField] using hasDerivAt_const x (1:ℂ)
    · simpa [zeroField] using Complex.ofRealCLM.hasDerivAt.const_mul (Complex.I*(k:ℂ))
  magnetic_derivative j x _ := by
    fin_cases j
    · simpa [zeroField] using hasDerivAt_const x (0:ℂ)
    · simpa [zeroField] using hasDerivAt_const x (1:ℂ)
  loss_integrable a b := continuous_const.intervalIntegrable a b
  passive _ := le_rfl

def negativeField (k x:ℝ) : Mat2 :=
  !![electricField k Complex.I 1 0 x,electricField k Complex.I 0 1 x;
     magneticField k Complex.I 1 0 x,magneticField k Complex.I 0 1 x]
def negativeProfile (k:ℝ) : Profile k where
  p := fun _=>-1
  q := fun _=>0
  interfaces := ∅
  field := negativeField k
  continuous i j := by
    fin_cases i <;> fin_cases j <;> simp [negativeField,electricField,magneticField] <;> fun_prop
  initial := by ext i j;fin_cases i <;> fin_cases j <;> simp [negativeField,electricField,magneticField]
  electric_derivative j x := by
    fin_cases j
    · simpa [negativeField] using electricField_hasDerivAt k Complex.I_ne_zero 1 0 x
    · simpa [negativeField] using electricField_hasDerivAt k Complex.I_ne_zero 0 1 x
  magnetic_derivative j x _ := by
    fin_cases j
    · simpa [negativeField,Complex.I_sq] using magneticField_hasDerivAt k Complex.I_ne_zero 1 0 x
    · simpa [negativeField,Complex.I_sq] using magneticField_hasDerivAt k Complex.I_ne_zero 0 1 x
  loss_integrable a b := continuous_const.intervalIntegrable a b
  passive _ := le_rfl

theorem zeroProfile_real (k x:ℝ) : (zeroProfile k).p x=0 := rfl
theorem negativeProfile_real (k x:ℝ) : (negativeProfile k).p x=-1 := rfl
theorem zeroProfile_loss (k x:ℝ) : (zeroProfile k).q x=0 := rfl
theorem negativeProfile_loss (k x:ℝ) : (negativeProfile k).q x=0 := rfl

end GeneralizedResearch.HelmholtzProfile
