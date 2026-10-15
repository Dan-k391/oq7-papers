import GeneralizedResearch.ProfileCellAggregation

/-! Literal unit-incidence cell absorption Gram matrices for the broad piecewise
Maxwell profile, with exact transmitted-power normalization. -/
noncomputable section
namespace GeneralizedResearch.HelmholtzProfile.Profile
open Set MeasureTheory OQ7
open scoped Matrix ComplexOrder
variable {k:ℝ} (F:Profile k)

def scatteringInput (D:ℝ) : Mat2 := inputFieldStates
  (transferReflectionLeft (waveTransfer (F.field D)))
  (transferTransmissionRight (waveTransfer (F.field D)))
def unitStates (D x:ℝ) : Mat2 := F.field x*F.scatteringInput D
def unitElectric (D:ℝ) (j:Fin 2) : ℝ→ℂ := F.electric (fun i=>F.scatteringInput D i j)
def unitMagnetic (D:ℝ) (j:Fin 2) : ℝ→ℂ := F.magnetic (fun i=>F.scatteringInput D i j)
def unitCellGram (D a b:ℝ) : Mat2 := (k:ℂ) • weightedGram (volume.restrict (Ioc a b)) F.q
  (fun x j=>F.unitElectric D j x)
def unitTransmission (D:ℝ) : ℂ := transferTransmissionRight (waveTransfer (F.field D))
def unitTotalAbsorption (D:ℝ) : Mat2 := absorptionMatrix
  (transferReflectionLeft (waveTransfer (F.field D)))
  (transferReflectionRight (waveTransfer (F.field D))) (F.unitTransmission D)

theorem unitStates_electric (D x:ℝ) (j:Fin 2) : F.unitStates D x 0 j=F.unitElectric D j x := by
  simp [unitStates,unitElectric,electric,Matrix.mul_apply,Fin.sum_univ_two]
theorem unitStates_magnetic (D x:ℝ) (j:Fin 2) : F.unitStates D x 1 j=F.unitMagnetic D j x := by
  simp [unitStates,unitMagnetic,magnetic,Matrix.mul_apply,Fin.sum_univ_two]

theorem unitElectric_derivative (D x:ℝ) (j:Fin 2) :
    HasDerivAt (F.unitElectric D j) (Complex.I*(k:ℂ)*F.unitMagnetic D j x) x :=
  F.electric_hasDerivAt _ x

theorem unitMagnetic_derivative (D x:ℝ) (j:Fin 2) (hx:x∉F.interfaces) :
    HasDerivAt (F.unitMagnetic D j)
      (Complex.I*(k:ℂ)*((F.p x:ℂ)+Complex.I*(F.q x:ℂ))*F.unitElectric D j x) x :=
  F.magnetic_hasDerivAt _ x hx

theorem unitStates_boundaries (hk:0≤k) {D:ℝ} (hD:0≤D) :
    F.unitStates D 0=F.scatteringInput D ∧
      F.unitStates D D=outputFieldStates (transferReflectionRight (waveTransfer (F.field D))) (F.unitTransmission D) := by
  constructor
  · simp [unitStates,F.initial]
  · exact F.scattering_boundary hk hD

theorem unitCellGram_entry (D:ℝ) {a b:ℝ} (hab:a≤b) (i j:Fin 2) :
    F.unitCellGram D a b i j=(k:ℂ)*∫x in a..b,
      (F.q x:ℂ)*star (F.unitElectric D i x)*F.unitElectric D j x := by
  rw [intervalIntegral.integral_of_le hab]
  rfl

/-- The Gram integral is transformed to actual unit incoming amplitudes; this
congruence is derived from the literal mixed Maxwell flux identity. -/
theorem unitCellGram_congruence (D:ℝ) {a b:ℝ} (hab:a≤b) :
    F.unitCellGram D a b=(1/2:ℂ) • ((F.scatteringInput D).conjTranspose*F.deposited a b*F.scatteringInput D) := by
  let B := F.scatteringInput D
  have hc : B.conjTranspose*F.deposited a b*B=
      (F.field a*B).conjTranspose*fluxForm*(F.field a*B)-
        (F.field b*B).conjTranspose*fluxForm*(F.field b*B) := by
    rw [F.deposited_flux hab]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  ext i j
  have hentry := congrFun (congrFun hc i) j
  rw [Matrix.sub_apply,←mixedFlux_matrix_entry,←mixedFlux_matrix_entry] at hentry
  change (B.conjTranspose*F.deposited a b*B) i j=
    mixedFlux (F.unitStates D a 0 i) (F.unitStates D a 1 i) (F.unitStates D a 0 j) (F.unitStates D a 1 j)-
    mixedFlux (F.unitStates D b 0 i) (F.unitStates D b 1 i) (F.unitStates D b 0 j) (F.unitStates D b 1 j) at hentry
  simp only [F.unitStates_electric,F.unitStates_magnetic] at hentry
  have hm := F.mixed_flux_integral (fun r=>B r i) (fun r=>B r j) hab
  change mixedFlux (F.unitElectric D i a) (F.unitMagnetic D i a) (F.unitElectric D j a) (F.unitMagnetic D j a)-
    mixedFlux (F.unitElectric D i b) (F.unitMagnetic D i b) (F.unitElectric D j b) (F.unitMagnetic D j b)=
      (2*(k:ℂ))*∫x in a..b,(F.q x:ℂ)*star (F.unitElectric D i x)*F.unitElectric D j x at hm
  rw [F.unitCellGram_entry D hab,Matrix.smul_apply,smul_eq_mul]
  change _=(1/2:ℂ)*((B.conjTranspose*F.deposited a b*B) i j)
  rw [hentry,hm]
  ring

theorem unitCellGram_posSemidef (hk:0≤k) (D:ℝ) {a b:ℝ} (hab:a≤b) :
    (F.unitCellGram D a b).PosSemidef := by
  rw [F.unitCellGram_congruence D hab]
  apply ((F.deposited_posSemidef hk a b).conjTranspose_mul_mul_same (F.scatteringInput D)).smul
  exact RCLike.nonneg_iff.mpr ⟨by norm_num,by norm_num⟩

theorem unitCellGram_det (D:ℝ) {a b:ℝ} (hab:a≤b) :
    (F.unitCellGram D a b).det=(Complex.normSq (F.unitTransmission D):ℂ)*(F.deposited a b).det := by
  rw [F.unitCellGram_congruence D hab,Matrix.det_smul,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_conjTranspose]
  simp only [Fintype.card_fin,scatteringInput,inputFieldStates_det]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [unitTransmission,map_mul,map_neg,map_ofNat,Complex.star_def]
  ring

theorem unitCellGram_normalized_det (hk:0≤k) {D a b:ℝ} (hD:0≤D) (hab:a≤b) :
    (F.unitCellGram D a b).det.re/transmissionPower (F.unitTransmission D)=(F.deposited a b).det.re := by
  have ht : F.unitTransmission D≠0 := F.transmission_ne_zero hk hD
  rw [F.unitCellGram_det D hab]
  simp only [transmissionPower,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_div_cancel_left₀ _ (Complex.normSq_pos.mpr ht).ne'

theorem unitCellGram_total (hk:0≤k) {D:ℝ} (hD:0≤D) :
    F.unitCellGram D 0 D=F.unitTotalAbsorption D := by
  rw [F.unitCellGram_congruence D hD,F.deposited_total hD]
  have hc := absorption_fluxDefect_congruence (F.field D) _ _ _ (F.scattering_boundary hk hD)
  change (2:ℂ) • F.unitTotalAbsorption D=
    (F.scatteringInput D).conjTranspose*fluxDefect (F.field D)*F.scatteringInput D at hc
  rw [←hc,smul_smul]
  norm_num

theorem lemma43_parameter_range (hk:0<k) {P Q a b:ℝ} (hP:0<P) (hQ:0<Q)
    (hq:∀z∈Ioo a b,0≤F.q z ∧ F.q z≤Q) (hab:a≤b)
    (hlength:b-a≤Real.pi/(k*Real.sqrt P)) :
    k*Real.sqrt P*(∫z in a..b,F.q z)/Q∈Icc (0:ℝ) Real.pi := by
  let K := k*Real.sqrt P
  have hK : 0<K := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hm0 : 0≤∫z in a..b,F.q z := intervalIntegral.integral_nonneg hab (fun z _=>F.passive z)
  have hm : (∫z in a..b,F.q z)≤(b-a)*Q := by
    simpa using intervalIntegral.integral_mono_on_of_le_Ioo hab (F.loss_integrable a b)
      (continuous_const.intervalIntegrable a b) (fun z hz=>(hq z hz).2)
  have hlen : K*(b-a)≤Real.pi := by
    have hh := (le_div_iff₀ hK).mp hlength
    nlinarith
  refine ⟨div_nonneg (mul_nonneg hK.le hm0) hQ.le,(div_le_iff₀ hQ).mpr ?_⟩
  calc
    K*(∫z in a..b,F.q z)≤K*((b-a)*Q) := mul_le_mul_of_nonneg_left hm hK.le
    _ = (K*(b-a))*Q := by ring
    _ ≤ Real.pi*Q := mul_le_mul_of_nonneg_right hlen hQ.le

/-- Original Lemma4.3 equation25 with the actual unit-incidence local absorption
matrix and actual transmitted power; selected material bounds impose no p lower bound. -/
theorem lemma43_cell (hk:0<k) {D P Q a b:ℝ} (hD:0≤D) (hP:0<P) (hQ:0<Q)
    (hp:∀z∈Ioo a b,F.p z≤P) (hq:∀z∈Ioo a b,0≤F.q z ∧ F.q z≤Q)
    (hab:a≤b) (hlength:b-a≤Real.pi/(k*Real.sqrt P)) :
    Q^2/P^2*ResourceScalar.f (k*Real.sqrt P*(∫z in a..b,F.q z)/Q)≤
      (F.unitCellGram D a b).det.re/transmissionPower (F.unitTransmission D) := by
  rw [F.unitCellGram_normalized_det hk.le hD hab]
  exact F.cell_det_lower hk hP hQ hp hq hab hlength

theorem lemma43_cell_sqrt (hk:0<k) {D P Q a b:ℝ} (hD:0≤D) (hP:0<P) (hQ:0<Q)
    (hp:∀z∈Ioo a b,F.p z≤P) (hq:∀z∈Ioo a b,0≤F.q z ∧ F.q z≤Q)
    (hab:a≤b) (hlength:b-a≤Real.pi/(k*Real.sqrt P)) :
    Q/P*ResourceScalar.g (k*Real.sqrt P*(∫z in a..b,F.q z)/Q)≤
      Real.sqrt ((F.unitCellGram D a b).det.re/transmissionPower (F.unitTransmission D)) := by
  rw [F.unitCellGram_normalized_det hk.le hD hab]
  exact F.cell_sqrt_det_lower hk hP hQ hp hq hab hlength


theorem unitTotal_normalized_det (hk:0≤k) {D:ℝ} (hD:0≤D) :
    (F.unitTotalAbsorption D).det.re/transmissionPower (F.unitTransmission D)=F.invariant D := by
  rw [F.invariant_scattering hk hD]
  rfl

theorem lemma43_combining {ι:Type*} (s:Finset ι) (a b:ι→ℝ) {D:ℝ} (hk:0≤k) (hD:0≤D)
    (hsub:∀j∈s,Ioc (a j) (b j)⊆Ioc 0 D)
    (hdis:Set.Pairwise (s:Set ι) (fun i j=>Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (hab:∀j∈s,a j≤b j) :
    (∑j∈s,Real.sqrt ((F.unitCellGram D (a j) (b j)).det.re/transmissionPower (F.unitTransmission D)))≤
      Real.sqrt ((F.unitTotalAbsorption D).det.re/transmissionPower (F.unitTransmission D)) := by
  have he : (∑j∈s,Real.sqrt ((F.unitCellGram D (a j) (b j)).det.re/transmissionPower (F.unitTransmission D)))=
      ∑j∈s,Real.sqrt ((F.deposited (a j) (b j)).det.re) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [F.unitCellGram_normalized_det hk hD (hab j hj)]
  rw [he,F.unitTotal_normalized_det hk hD]
  exact F.disjoint_sqrt_aggregate s a b hk hD hsub hdis

/-- Literal original Lemma4.3: actual unit-incidence A_j, actual T>0, the
parameter interval, both equation25 cell bound and equation26 for arbitrary
finite disjoint cells, including all absorption outside the selected union. -/
theorem lemma43 {ι:Type*} (s:Finset ι) (a b:ι→ℝ) {D P Q:ℝ}
    (hk:0<k) (hD:0≤D) (hP:0<P) (hQ:0<Q)
    (hsub:∀j∈s,Ioc (a j) (b j)⊆Ioc 0 D)
    (hdis:Set.Pairwise (s:Set ι) (fun i j=>Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (hab:∀j∈s,a j≤b j)
    (hwidth:∀j∈s,b j-a j≤Real.pi/(k*Real.sqrt P))
    (hp:∀j∈s,∀z∈Ioo (a j) (b j),F.p z≤P)
    (hq:∀j∈s,∀z∈Ioo (a j) (b j),0≤F.q z ∧ F.q z≤Q) :
    0<transmissionPower (F.unitTransmission D) ∧
    (∀j∈s,k*Real.sqrt P*(∫z in a j..b j,F.q z)/Q∈Icc (0:ℝ) Real.pi ∧
      Q^2/P^2*ResourceScalar.f (k*Real.sqrt P*(∫z in a j..b j,F.q z)/Q)≤
        (F.unitCellGram D (a j) (b j)).det.re/transmissionPower (F.unitTransmission D)) ∧
    Q/P*(∑j∈s,ResourceScalar.g (k*Real.sqrt P*(∫z in a j..b j,F.q z)/Q))≤
      Real.sqrt ((F.unitTotalAbsorption D).det.re/transmissionPower (F.unitTransmission D)) := by
  refine ⟨Complex.normSq_pos.mpr (F.transmission_ne_zero hk.le hD),?_,?_⟩
  · intro j hj
    exact ⟨F.lemma43_parameter_range hk hP hQ (hq j hj) (hab j hj) (hwidth j hj),
      F.lemma43_cell hk hD hP hQ (hp j hj) (hq j hj) (hab j hj) (hwidth j hj)⟩
  · rw [F.unitTotal_normalized_det hk.le hD]
    exact F.disjoint_resource_cells s a b hk hP hQ hD hsub hdis hab hwidth hp hq

end GeneralizedResearch.HelmholtzProfile.Profile
