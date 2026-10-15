import OQ7.ModulusComparison
import OQ7.PhysicalAbsorption
import OQ7.Passivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A literal piecewise Maxwell/Helmholtz profile with no lower bound on the
real permittivity. The structure stores differential equations and ordinary
regularity only. Unimodularity, flux/Gram identities, scattering passivity and
nonzero transmission are derived, not included as structure assumptions. -/

noncomputable section
namespace GeneralizedResearch.HelmholtzProfile
open Set MeasureTheory OQ7
open scoped Matrix ComplexOrder Topology

theorem integral_eq_sub_off_finset (bad : Finset ℝ) {f g : ℝ→ℂ}
    (hcont : Continuous f) (hint : ∀ x y, IntervalIntegrable g volume x y)
    {a b : ℝ} (hab : a≤b)
    (hderiv : ∀ x∈Ioo a b, x∉bad → HasDerivAt f (g x) x) :
    (∫ x in a..b,g x)=f b-f a := by
  classical
  induction bad using Finset.induction_on generalizing a b with
  | empty =>
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont.continuousOn
      (fun x hx => hderiv x hx (by simp)) (hint a b)
  | @insert c bad hc ih =>
    have hsub (x y : ℝ) (hx : a≤x) (hy : y≤b) (hxy : x≤y)
        (hnotc : ∀ z∈Ioo x y,z≠c) : (∫ z in x..y,g z)=f y-f x := by
      apply ih hxy
      intro z hz hzb
      apply hderiv z ⟨hx.trans_lt hz.1,hz.2.trans_le hy⟩
      simp only [Finset.mem_insert,not_or]
      exact ⟨hnotc z hz,hzb⟩
    by_cases hca : c≤a
    · exact hsub a b le_rfl le_rfl hab (fun z hz => (hca.trans_lt hz.1).ne')
    by_cases hbc : b≤c
    · exact hsub a b le_rfl le_rfl hab (fun z hz => (hz.2.trans_le hbc).ne)
    have hac : a<c := lt_of_not_ge hca
    have hcb : c<b := lt_of_not_ge hbc
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint a c) (hint c b),
      hsub a c le_rfl hcb.le hac.le (fun z hz => hz.2.ne),
      hsub c b hac.le le_rfl hcb.le (fun z hz => hz.1.ne')]
    ring

structure Profile (k : ℝ) where
  p : ℝ→ℝ
  q : ℝ→ℝ
  interfaces : Finset ℝ
  field : ℝ→Mat2
  continuous : ∀ i j,Continuous (fun x => field x i j)
  initial : field 0=1
  electric_derivative : ∀ j x,HasDerivAt (fun y=>field y 0 j) (Complex.I*(k:ℂ)*field x 1 j) x
  magnetic_derivative : ∀ j x,x∉interfaces → HasDerivAt (fun y=>field y 1 j)
    (Complex.I*(k:ℂ)*((p x:ℂ)+Complex.I*(q x:ℂ))*field x 0 j) x
  loss_integrable : ∀ a b,IntervalIntegrable q volume a b
  passive : ∀ x,0≤q x

namespace Profile
variable {k : ℝ} (F : Profile k)

def electric (u : Fin 2→ℂ) (x : ℝ) : ℂ := F.field x 0 0*u 0+F.field x 0 1*u 1
def magnetic (u : Fin 2→ℂ) (x : ℝ) : ℂ := F.field x 1 0*u 0+F.field x 1 1*u 1

theorem electric_continuous (u : Fin 2→ℂ) : Continuous (F.electric u) :=
  ((F.continuous 0 0).mul continuous_const).add ((F.continuous 0 1).mul continuous_const)
theorem magnetic_continuous (u : Fin 2→ℂ) : Continuous (F.magnetic u) :=
  ((F.continuous 1 0).mul continuous_const).add ((F.continuous 1 1).mul continuous_const)
theorem electric_hasDerivAt (u : Fin 2→ℂ) (x : ℝ) :
    HasDerivAt (F.electric u) (Complex.I*(k:ℂ)*F.magnetic u x) x := by
  convert ((F.electric_derivative 0 x).mul_const (u 0)).add
    ((F.electric_derivative 1 x).mul_const (u 1)) using 1
  · rfl
  · dsimp [magnetic]
    ring
theorem magnetic_hasDerivAt (u : Fin 2→ℂ) (x : ℝ) (hx : x∉F.interfaces) :
    HasDerivAt (F.magnetic u)
      (Complex.I*(k:ℂ)*((F.p x:ℂ)+Complex.I*(F.q x:ℂ))*F.electric u x) x := by
  convert ((F.magnetic_derivative 0 x hx).mul_const (u 0)).add
    ((F.magnetic_derivative 1 x hx).mul_const (u 1)) using 1
  · rfl
  · dsimp [electric]
    ring

theorem electric_initial (u : Fin 2→ℂ) : F.electric u 0=u 0 := by
  simp [electric,F.initial]
theorem magnetic_initial (u : Fin 2→ℂ) : F.magnetic u 0=u 1 := by
  simp [magnetic,F.initial]

theorem field_det (x : ℝ) : (F.field x).det=1 := by
  have hcont : Continuous (fun y=>(F.field y).det) := by
    simp only [Matrix.det_fin_two]
    exact ((F.continuous 0 0).mul (F.continuous 1 1)).sub
      ((F.continuous 0 1).mul (F.continuous 1 0))
  have hd (y : ℝ) (hy : y∉F.interfaces) : HasDerivAt (fun z=>(F.field z).det) 0 y := by
    convert ((F.electric_derivative 0 y).mul (F.magnetic_derivative 1 y hy)).sub
      ((F.electric_derivative 1 y).mul (F.magnetic_derivative 0 y hy)) using 1
    · funext z
      simp only [Matrix.det_fin_two,Pi.mul_apply,Pi.sub_apply]
    · ring
  have hzero (a b : ℝ) (hab : a≤b) : (F.field b).det=(F.field a).det := by
    have h := integral_eq_sub_off_finset F.interfaces hcont
      (fun a b=>continuous_const.intervalIntegrable a b) hab (fun y _ hy=>hd y hy)
    exact sub_eq_zero.mp (by simpa using h.symm)
  rcases le_total 0 x with hx|hx
  · simpa [F.initial] using hzero 0 x hx
  · simpa [F.initial] using (hzero x 0 hx).symm

theorem loss_complex_integrable (a b : ℝ) :
    IntervalIntegrable (fun x=>(F.q x:ℂ)) volume a b :=
  ⟨Complex.ofRealCLM.integrable_comp (F.loss_integrable a b).1,
   Complex.ofRealCLM.integrable_comp (F.loss_integrable a b).2⟩

def weighted (u v : Fin 2→ℂ) (x : ℝ) : ℂ :=
  (F.q x:ℂ)*star (F.electric u x)*F.electric v x

theorem weighted_integrable (u v : Fin 2→ℂ) (a b : ℝ) :
    IntervalIntegrable (F.weighted u v) volume a b := by
  exact ((F.loss_complex_integrable a b).mul_continuousOn
    (F.electric_continuous u).star.continuousOn).mul_continuousOn (F.electric_continuous v).continuousOn

theorem mixed_flux_integral (u v : Fin 2→ℂ) {a b : ℝ} (hab : a≤b) :
    mixedFlux (F.electric u a) (F.magnetic u a) (F.electric v a) (F.magnetic v a)-
      mixedFlux (F.electric u b) (F.magnetic u b) (F.electric v b) (F.magnetic v b)=
      (2*(k:ℂ))*(∫ x in a..b,F.weighted u v x) := by
  have hcont : Continuous (fun x=>mixedFlux (F.electric u x) (F.magnetic u x)
      (F.electric v x) (F.magnetic v x)) := by
    unfold mixedFlux
    exact ((F.electric_continuous u).star.mul (F.magnetic_continuous v)).add
      ((F.magnetic_continuous u).star.mul (F.electric_continuous v))
  have hint (x y : ℝ) : IntervalIntegrable (fun z=>(-2*(k:ℂ))*F.weighted u v z) volume x y :=
    (F.weighted_integrable u v x y).const_mul _
  have hd (x : ℝ) (hx : x∉F.interfaces) := maxwellMixedFlux_hasDerivAt k (F.p x) (F.q x)
    (F.electric u) (F.magnetic u) (F.electric v) (F.magnetic v) x
    (F.electric_hasDerivAt u x) (F.magnetic_hasDerivAt u x hx)
    (F.electric_hasDerivAt v x) (F.magnetic_hasDerivAt v x hx)
  have h := integral_eq_sub_off_finset F.interfaces hcont hint hab (by
    intro x _ hx
    convert hd x hx using 1
    dsimp [weighted]
    ring)
  rw [intervalIntegral.integral_const_mul] at h
  linear_combination h

def deposited (a b : ℝ) : Mat2 :=
  (2*(k:ℂ)) • weightedGram (volume.restrict (Ioc a b)) F.q (fun x j=>F.field x 0 j)

theorem basis_electric (j : Fin 2) (x : ℝ) :
    F.electric (fun i=>(1:Mat2) i j) x=F.field x 0 j := by
  fin_cases j <;> norm_num [electric,Matrix.one_apply]
theorem basis_magnetic (j : Fin 2) (x : ℝ) :
    F.magnetic (fun i=>(1:Mat2) i j) x=F.field x 1 j := by
  fin_cases j <;> norm_num [magnetic,Matrix.one_apply]

theorem weighted_entry_integrable (i j : Fin 2) (a b : ℝ) :
    IntervalIntegrable (fun x=>(F.q x:ℂ)*star (F.field x 0 i)*F.field x 0 j) volume a b := by
  have h := F.weighted_integrable (fun r=>(1:Mat2) r i) (fun r=>(1:Mat2) r j) a b
  change IntervalIntegrable (fun x=>F.weighted (fun r=>(1:Mat2) r i)
    (fun r=>(1:Mat2) r j) x) volume a b at h
  simpa only [weighted,basis_electric] using h

theorem deposited_entry {a b : ℝ} (hab : a≤b) (i j : Fin 2) :
    F.deposited a b i j=(2*(k:ℂ))*∫ x in a..b,(F.q x:ℂ)*star (F.field x 0 i)*F.field x 0 j := by
  rw [intervalIntegral.integral_of_le hab]
  rfl

theorem deposited_flux {a b : ℝ} (hab : a≤b) :
    F.deposited a b=(F.field a).conjTranspose*fluxForm*F.field a-
      (F.field b).conjTranspose*fluxForm*F.field b := by
  ext i j
  have h := F.mixed_flux_integral (fun r=>(1:Mat2) r i) (fun r=>(1:Mat2) r j) hab
  simp only [basis_electric,basis_magnetic,mixedFlux_matrix_entry] at h
  simpa only [deposited_entry F hab,weighted,basis_electric,Matrix.sub_apply] using h.symm

theorem deposited_total {D : ℝ} (hD : 0≤D) : F.deposited 0 D=fluxDefect (F.field D) := by
  rw [F.deposited_flux hD,F.initial]
  simp [fluxDefect]

theorem deposited_posSemidef (hk : 0≤k) (a b : ℝ) : (F.deposited a b).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · apply weightedGram_posSemidef
    · intro i j
      exact (F.weighted_entry_integrable i j a b).1
    · exact ae_of_all _ F.passive
  · exact RCLike.nonneg_iff.mpr ⟨by simpa using mul_nonneg (by norm_num : (0:ℝ)≤2) hk,by simp⟩

theorem transfer_passive (hk : 0≤k) {D : ℝ} (hD : 0≤D) : (fluxDefect (F.field D)).PosSemidef := by
  rw [← F.deposited_total hD]
  exact F.deposited_posSemidef hk 0 D

theorem scattering_passive (hk : 0≤k) {D : ℝ} (hD : 0≤D) :
    Passive (transferReflectionLeft (waveTransfer (F.field D)))
      (transferReflectionRight (waveTransfer (F.field D)))
      (transferTransmissionRight (waveTransfer (F.field D))) :=
  passive_transfer_scattering _ (F.transfer_passive hk hD) (F.field_det D)

theorem transmission_ne_zero (hk : 0≤k) {D : ℝ} (hD : 0≤D) :
    transferTransmissionRight (waveTransfer (F.field D))≠0 :=
  passive_transfer_transmission_ne_zero _ (F.transfer_passive hk hD)

/-- The actual Maxwell field matrix yields the standard unit-incident,
outgoing-wave boundary states in identical vacuum exteriors. -/
theorem scattering_boundary (hk : 0≤k) {D : ℝ} (hD : 0≤D) :
    F.field D*inputFieldStates (transferReflectionLeft (waveTransfer (F.field D)))
      (transferTransmissionRight (waveTransfer (F.field D)))=
    outputFieldStates (transferReflectionRight (waveTransfer (F.field D)))
      (transferTransmissionRight (waveTransfer (F.field D))) :=
  field_transfer_boundary_states _
    (passive_transfer_denominator_ne_zero _ (F.transfer_passive hk hD)) (F.field_det D)

def invariant (D : ℝ) : ℝ := (fluxDefect (F.field D)).det.re

theorem invariant_scattering (hk : 0≤k) {D : ℝ} (hD : 0≤D) :
    F.invariant D=normalizedAbsorptionDet (transferReflectionLeft (waveTransfer (F.field D)))
      (transferReflectionRight (waveTransfer (F.field D)))
      (transferTransmissionRight (waveTransfer (F.field D))) := by
  have h := congrArg Complex.re (passive_transfer_absorption_det_ratio _
    (F.transfer_passive hk hD) (F.field_det D))
  simpa [invariant,normalizedAbsorptionDet,transmissionPower,Complex.div_ofReal_re] using h.symm

end Profile
end GeneralizedResearch.HelmholtzProfile
