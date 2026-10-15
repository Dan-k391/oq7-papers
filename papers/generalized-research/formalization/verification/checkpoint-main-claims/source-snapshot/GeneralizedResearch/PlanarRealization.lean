import GeneralizedResearch.PlanarFourPort
import GeneralizedResearch.PlanarPlateBridge
import PrescribedExtinction.PlanarSlabChannels

/-! Explicit Maxwell fields for the absorbing and vacuum channels. The
four-port boundary response is connected to these actual differential fields,
rather than postulated as a property of an abstract physical structure. -/

noncomputable section
namespace GeneralizedResearch.PlanarRealization
open OQ7Prescribed
open scoped Matrix ComplexOrder

def vacuumLayer (k h : ℝ) (L R : ℂ) : PlanarLayerField k 0 h := by
  let f : ℝ → ℂ := fun x => apertureOscillation k x * L
  let g : ℝ → ℂ := fun x => apertureOscillation k (h-x) * R
  have hf (x : ℝ) : HasDerivAt f (Complex.I*(k:ℂ)*f x) x := by
    convert (apertureOscillation_hasDerivAt k x).mul_const L using 1
    dsimp [f]
    ring
  have hg (x : ℝ) : HasDerivAt g (-(Complex.I*(k:ℂ))*g x) x := by
    have hd := ((apertureOscillation_hasDerivAt k (h-x)).scomp x
      ((hasDerivAt_const x h).sub (hasDerivAt_id x))).mul_const R
    convert hd using 1
    all_goals simp [g]
    all_goals ring
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  refine ⟨fun x => f x+g x,fun x => f x-g x,fun _ => 0,
    (hfc.add hgc).continuousOn,(hfc.sub hgc).continuousOn,continuousOn_const,?_,?_⟩
  · intro x _
    convert (hf x).add (hg x) using 1
    ring
  · intro x _
    convert (hf x).sub (hg x) using 1
    ring

theorem vacuum_boundary (k h : ℝ) (L R : ℂ) :
    (vacuumLayer k h L R).electric 0=L+apertureOscillation k h*R ∧
    (vacuumLayer k h L R).magnetic 0=L-apertureOscillation k h*R ∧
    (vacuumLayer k h L R).electric h=apertureOscillation k h*L+R ∧
    (vacuumLayer k h L R).magnetic h=apertureOscillation k h*L-R := by
  simp [vacuumLayer,apertureOscillation]

theorem vacuum_current (k h : ℝ) (L R : ℂ) (x : ℝ) :
    (vacuumLayer k h L R).current x=0 := rfl

def absorbingLayer (k η h : ℝ) (L R : ℂ) : PlanarLayerField k 0 h :=
  ((dielectricSlabLeftAt k 1 η 0 h le_rfl).const_mul L).add
    ((dielectricSlabRightAt k 1 η 0 h le_rfl).const_mul R)

theorem absorbing_boundary (k η h : ℝ) (hk : 0<k) (hη : 0≤η) (hh : 0≤h) (L R : ℂ) :
    let r := dielectricSlabReflection k 1 η h
    let τ := dielectricSlabTransmission k 1 η h
    (absorbingLayer k η h L R).electric 0=L+(r*L+τ*R) ∧
    (absorbingLayer k η h L R).magnetic 0=L-(r*L+τ*R) ∧
    (absorbingLayer k η h L R).electric h=(τ*L+r*R)+R ∧
    (absorbingLayer k η h L R).magnetic h=(τ*L+r*R)-R := by
  have hl := dielectricSlabLeftAt_boundary k hk 1 η 0 h le_rfl hη hh
  have hr := dielectricSlabRightAt_boundary k hk 1 η 0 h le_rfl hη hh
  dsimp
  simp only [absorbingLayer,PlanarLayerField.add,PlanarLayerField.const_mul]
  simp only [sub_zero] at hl hr
  rw [hl.1,hl.2.1,hl.2.2.1,hl.2.2.2,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2]
  exact ⟨by ring,by ring,by ring,by ring⟩

theorem absorbing_constitutive (k η h : ℝ) (L R : ℂ) (x : ℝ) :
    (absorbingLayer k η h L R).current x=
      Complex.I*(η:ℂ)*(absorbingLayer k η h L R).electric x := by
  simp only [absorbingLayer,PlanarLayerField.add,PlanarLayerField.const_mul]
  rw [dielectricSlabLeftAt_constitutive,dielectricSlabRightAt_constitutive]
  push_cast
  ring

def internalX (t s : ℝ) (a : PlanarFourPort.Vec4) : ℂ := (t:ℂ)*a 2-(s:ℂ)*a 3
def internalY (t s : ℝ) (a : PlanarFourPort.Vec4) : ℂ := -(s:ℂ)*a 2-(t:ℂ)*a 3
def beforeX (r τ : ℂ) (t s : ℝ) (a : PlanarFourPort.Vec4) : ℂ :=
  τ*a 0+r*internalX t s a
def beforeY (z : ℂ) (a : PlanarFourPort.Vec4) : ℂ := z*a 1

theorem scattering_action (r τ z : ℂ) (t s : ℝ) (a : PlanarFourPort.Vec4) :
    PlanarFourPort.scattering r τ z t s *ᵥ a =
      ![r*a 0+τ*internalX t s a,z*internalY t s a,
        (t:ℂ)*beforeX r τ t s a-(s:ℂ)*beforeY z a,
        -(s:ℂ)*beforeX r τ t s a-(t:ℂ)*beforeY z a] := by
  rw [PlanarFourPort.scattering_formula]
  ext i; fin_cases i <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,internalX,internalY,beforeX,beforeY] <;> ring

def slabR (k η h : ℝ) : ℂ := dielectricSlabReflection k 1 η h
def slabT (k η h : ℝ) : ℂ := dielectricSlabTransmission k 1 η h
def phase (k h : ℝ) : ℂ := apertureOscillation k h
def response (k η h t : ℝ) : PlanarFourPort.Mat4 :=
  PlanarFourPort.scattering (slabR k η h) (slabT k η h) (phase k h) t (PlanarPlateBridge.s t)
def absorberX (k η h t : ℝ) (a : PlanarFourPort.Vec4) : PlanarLayerField k 0 h :=
  absorbingLayer k η h (a 0) (internalX t (PlanarPlateBridge.s t) a)
def absorberY (k h t : ℝ) (a : PlanarFourPort.Vec4) : PlanarLayerField k 0 h :=
  vacuumLayer k h (a 1) (internalY t (PlanarPlateBridge.s t) a)
def plateX (k η h : ℝ) (j : ℕ) (hj : 1≤j) (t : ℝ) (a : PlanarFourPort.Vec4) :
    PlanarLayerField k h (h+plateDesignThickness k j) :=
  PlanarPlateBridge.xLayer k h j hj t
    (beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a + internalX t (PlanarPlateBridge.s t) a)
    (beforeY (phase k h) a + internalY t (PlanarPlateBridge.s t) a)
    (beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a - internalX t (PlanarPlateBridge.s t) a)
    (beforeY (phase k h) a - internalY t (PlanarPlateBridge.s t) a)
def plateY (k η h : ℝ) (j : ℕ) (hj : 1≤j) (t : ℝ) (a : PlanarFourPort.Vec4) :
    PlanarLayerField k h (h+plateDesignThickness k j) :=
  PlanarPlateBridge.yLayer k h j hj t
    (beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a + internalX t (PlanarPlateBridge.s t) a)
    (beforeY (phase k h) a + internalY t (PlanarPlateBridge.s t) a)
    (beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a - internalX t (PlanarPlateBridge.s t) a)
    (beforeY (phase k h) a - internalY t (PlanarPlateBridge.s t) a)

theorem plate_initial (k η h : ℝ) (j : ℕ) (hj : 1≤j) (t : ℝ)
    (ht0 : -1≤t) (ht1 : t≤1) (a : PlanarFourPort.Vec4) :
    (plateX k η h j hj t a).electric h=
      beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a+internalX t (PlanarPlateBridge.s t) a ∧
    (plateY k η h j hj t a).electric h=
      beforeY (phase k h) a+internalY t (PlanarPlateBridge.s t) a ∧
    (plateX k η h j hj t a).magnetic h=
      beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a-internalX t (PlanarPlateBridge.s t) a ∧
    (plateY k η h j hj t a).magnetic h=
      beforeY (phase k h) a-internalY t (PlanarPlateBridge.s t) a :=
  PlanarPlateBridge.initial_boundary k h j hj ht0 ht1 _ _ _ _

/-- Literal electric and magnetic interface continuity, for every incident
four-port vector and the actual scalar-slab and rotated-plate fields. -/
theorem interface_continuity (k η h : ℝ) (hk : 0<k) (hη : 0≤η) (hh : 0≤h)
    (j : ℕ) (hj : 1≤j) (t : ℝ) (ht0 : -1≤t) (ht1 : t≤1) (a : PlanarFourPort.Vec4) :
    (absorberX k η h t a).electric h=(plateX k η h j hj t a).electric h ∧
    (absorberY k h t a).electric h=(plateY k η h j hj t a).electric h ∧
    (absorberX k η h t a).magnetic h=(plateX k η h j hj t a).magnetic h ∧
    (absorberY k h t a).magnetic h=(plateY k η h j hj t a).magnetic h := by
  have ha := absorbing_boundary k η h hk hη hh (a 0) (internalX t (PlanarPlateBridge.s t) a)
  have hv := vacuum_boundary k h (a 1) (internalY t (PlanarPlateBridge.s t) a)
  have hw := plate_initial k η h j hj t ht0 ht1 a
  exact ⟨ha.2.2.1.trans hw.1.symm,hv.2.2.1.trans hw.2.1.symm,
    ha.2.2.2.trans hw.2.2.1.symm,hv.2.2.2.trans hw.2.2.2.symm⟩

/-- The actual left boundary has the prescribed incident amplitudes and
the outgoing amplitudes of the derived four-port scattering matrix. -/
theorem left_boundary (k η h : ℝ) (hk : 0<k) (hη : 0≤η) (hh : 0≤h)
    (t : ℝ) (a : PlanarFourPort.Vec4) :
    let b := response k η h t *ᵥ a
    (absorberX k η h t a).electric 0=a 0+b 0 ∧
    (absorberY k h t a).electric 0=a 1+b 1 ∧
    (absorberX k η h t a).magnetic 0=a 0-b 0 ∧
    (absorberY k h t a).magnetic 0=a 1-b 1 := by
  have ha := absorbing_boundary k η h hk hη hh (a 0) (internalX t (PlanarPlateBridge.s t) a)
  have hv := vacuum_boundary k h (a 1) (internalY t (PlanarPlateBridge.s t) a)
  dsimp only [response]
  rw [scattering_action]
  exact ⟨ha.1,hv.1,ha.2.1,hv.2.1⟩

/-- The actual plate's right boundary gives the same outgoing vector, with
the externally imposed incoming vector. Together with the other two boundary
theorems and the PlanarLayerField derivative fields, this proves realization
by the two Maxwell layers for arbitrary four-port illumination. -/
theorem right_boundary (k η h : ℝ) (hk : 0<k) (j : ℕ) (hj : 1≤j)
    (t : ℝ) (ht0 : -1≤t) (ht1 : t≤1) (a : PlanarFourPort.Vec4) :
    let b := response k η h t *ᵥ a
    let endPoint := h+plateDesignThickness k j
    (plateX k η h j hj t a).electric endPoint=b 2+a 2 ∧
    (plateY k η h j hj t a).electric endPoint=b 3+a 3 ∧
    (plateX k η h j hj t a).magnetic endPoint=b 2-a 2 ∧
    (plateY k η h j hj t a).magnetic endPoint=b 3-a 3 := by
  have hw := PlanarPlateBridge.final_boundary k hk h j hj ht0 ht1
    (beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a + internalX t (PlanarPlateBridge.s t) a)
    (beforeY (phase k h) a + internalY t (PlanarPlateBridge.s t) a)
    (beforeX (slabR k η h) (slabT k η h) t (PlanarPlateBridge.s t) a - internalX t (PlanarPlateBridge.s t) a)
    (beforeY (phase k h) a - internalY t (PlanarPlateBridge.s t) a)
  have hs : t^2+(PlanarPlateBridge.s t)^2=1 := by
    dsimp [PlanarPlateBridge.s]
    rw [Real.sq_sqrt (by nlinarith : 0≤1-t^2)]
    ring
  have hc : (t:ℂ)^2+(PlanarPlateBridge.s t:ℂ)^2=1 := by exact_mod_cast hs
  dsimp only [response]
  rw [scattering_action]
  change _ ∧ _ ∧ _ ∧ _
  constructor
  · rw [show (plateX k η h j hj t a).electric _ = _ from hw.1]
    dsimp [internalX,internalY]
    linear_combination (a 2)*hc
  constructor
  · rw [show (plateY k η h j hj t a).electric _ = _ from hw.2.1]
    dsimp [internalX,internalY]
    linear_combination (a 3)*hc
  constructor
  · rw [show (plateX k η h j hj t a).magnetic _ = _ from hw.2.2.1]
    dsimp [internalX,internalY]
    linear_combination -(a 2)*hc
  · rw [show (plateY k η h j hj t a).magnetic _ = _ from hw.2.2.2]
    dsimp [internalX,internalY]
    linear_combination -(a 3)*hc

theorem absorber_constitutive (k η h t : ℝ) (a : PlanarFourPort.Vec4) (x : ℝ) :
    (absorberX k η h t a).current x=Complex.I*(η:ℂ)*(absorberX k η h t a).electric x ∧
      (absorberY k h t a).current x=0 :=
  ⟨absorbing_constitutive k η h _ _ x,rfl⟩

theorem plate_phase (k : ℝ) (hk : 0<k) (j : ℕ) (hj : 1≤j) :
    apertureOscillation k (plateDesignThickness k j)=-1 := by
  have hp := (plateDesign_phases k hk.ne' j hj).1
  have hc : ((k*plateDesignThickness k j:ℝ):ℂ)=
      (j:ℂ)*(2*(Real.pi:ℂ))-(Real.pi:ℂ) := by exact_mod_cast hp
  unfold apertureOscillation
  rw [mul_comm Complex.I,Complex.exp_mul_I,hc]
  simp [Complex.cos_nat_mul_two_pi_sub_pi,Complex.sin_nat_mul_two_pi_sub]

/-- The matrix reference is exactly propagation through vacuum across the
full two-layer length, including the chosen odd-half-wave plate width. -/
theorem reference_vacuum (k h : ℝ) (hk : 0<k) (j : ℕ) (hj : 1≤j) :
    PlanarFourPort.reference (phase k h)=
      apertureOscillation k (h+plateDesignThickness k j) •
        (!![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]:PlanarFourPort.Mat4) := by
  rw [apertureOscillation_add,plate_phase k hk j hj,mul_neg_one]
  ext i l; fin_cases i <;> fin_cases l <;> simp [PlanarFourPort.reference,phase]

theorem phase_unitary (k h : ℝ) : star (phase k h)*phase k h=1 := by
  have hn := apertureOscillation_norm k h
  have hsq : Complex.normSq (phase k h)=1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp only [phase,hn,one_pow]
  calc
    star (phase k h)*phase k h=(Complex.normSq (phase k h):ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    _ = 1 := by rw [hsq]; rfl

theorem response_passive (k η h : ℝ) (hk : 0<k) (hη : 0≤η) (hh : 0≤h)
    (t : ℝ) (ht0 : -1≤t) (ht1 : t≤1) :
    ((1:PlanarFourPort.Mat4)-(response k η h t).conjTranspose*response k η h t).PosSemidef := by
  have hs : t^2+(PlanarPlateBridge.s t)^2=1 := by
    dsimp [PlanarPlateBridge.s]
    rw [Real.sq_sqrt (by nlinarith : 0≤1-t^2)]
    ring
  exact PlanarFourPort.scattering_passive _ _ _ t _ hs (phase_unitary k h)
    (dielectricSlab_passive k hk 1 η h le_rfl hη hh)

theorem physical_power_values (k η h : ℝ) (t : ℝ) (ht0 : -1≤t) (ht1 : t≤1) :
    ChannelPowers.absorption (response k η h t) PlanarFourPort.left=0 ∧
    ChannelPowers.absorption (response k η h t)
      (ChannelPowers.reverse (PlanarFourPort.reference (phase k h)) PlanarFourPort.left)=
      (1-t^2)*OQ7.absorptanceLeft (slabR k η h) (slabT k η h) := by
  have hs : t^2+(PlanarPlateBridge.s t)^2=1 := by
    dsimp [PlanarPlateBridge.s]
    rw [Real.sq_sqrt (by nlinarith : 0≤1-t^2)]
    ring
  exact ⟨(PlanarFourPort.power_values _ _ _ t _ hs (phase_unitary k h)).1,
    PlanarFourPort.reversed_absorption _ _ _ t _ hs (phase_unitary k h)⟩

theorem physical_extinction_values (k η h t : ℝ) :
    ChannelPowers.extinction (response k η h t) (PlanarFourPort.reference (phase k h)) PlanarFourPort.left=2*(1-t) ∧
    ChannelPowers.extinction (response k η h t) (PlanarFourPort.reference (phase k h))
      (ChannelPowers.reverse (PlanarFourPort.reference (phase k h)) PlanarFourPort.left)=2*(1-t) :=
  PlanarFourPort.extinction_values _ _ _ t _ (phase_unitary k h)

end GeneralizedResearch.PlanarRealization
