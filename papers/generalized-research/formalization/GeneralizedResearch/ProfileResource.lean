import GeneralizedResearch.ProfileGram
import OQ7.ResourceBounds
import OQ7.ResourceUniform

/-! Original broad selected-interval resource theorem in the literal
piecewise Maxwell profile model. Real permittivity has no global lower bound.
All cell floors are derived from the actual differential fields, and material
caps apply only on the selected interval; exterior passive layers are allowed. -/

noncomputable section
namespace GeneralizedResearch.HelmholtzProfile.Profile
open Set MeasureTheory OQ7 Filter
open scoped Matrix ComplexOrder Topology
variable {k : ℝ} (F : Profile k)

theorem deposited_add {a b c : ℝ} (hab : a≤b) (hbc : b≤c) :
    F.deposited a c=F.deposited a b+F.deposited b c := by
  rw [F.deposited_flux (hab.trans hbc),F.deposited_flux hab,F.deposited_flux hbc]
  abel

def cellAbsorption (a L : ℝ) (n : ℕ) (j : Fin n) : Mat2 :=
  F.deposited (resourceCellPoint a L n j.val) (resourceCellPoint a L n (j.val+1))

theorem cellAbsorption_sum (a : ℝ) {L : ℝ} (hL : 0≤L) {n : ℕ} (hn : 0<n) :
    (∑ j:Fin n,F.cellAbsorption a L n j)=F.deposited a (a+L) := by
  ext i j
  simp only [Matrix.sum_apply]
  have heq (r : Fin n) : F.cellAbsorption a L n r i j=
      (2*(k:ℂ))*∫ z in resourceCellPoint a L n r.val..resourceCellPoint a L n (r.val+1),
        (F.q z:ℂ)*star (F.field z 0 i)*F.field z 0 j :=
    F.deposited_entry (resourceCellPoint_le_next a hL n r.val) i j
  simp_rw [heq]
  rw [← Finset.mul_sum,F.deposited_entry (by linarith : a≤a+L)]
  congr 1
  have hs := Fin.sum_univ_eq_sum_range (fun r:ℕ=>∫ z in resourceCellPoint a L n r..
    resourceCellPoint a L n (r+1),(F.q z:ℂ)*star (F.field z 0 i)*F.field z 0 j) n
  rw [hs,intervalIntegral.sum_integral_adjacent_intervals
    (fun r hr=>F.weighted_entry_integrable i j _ _),resourceCellPoint_zero,resourceCellPoint_end a L hn]

theorem selected_rest_posSemidef (hk : 0≤k) {a L D : ℝ} (ha : 0≤a) (hL : 0≤L)
    (hend : a+L≤D) {n : ℕ} (hn : 0<n) :
    (fluxDefect (F.field D)-∑ j:Fin n,F.cellAbsorption a L n j).PosSemidef := by
  have hab : a≤a+L := by linarith
  have hD : 0≤D := by linarith
  rw [F.cellAbsorption_sum a hL hn,← F.deposited_total hD]
  have he : F.deposited 0 D-F.deposited a (a+L)=F.deposited 0 a+F.deposited (a+L) D := by
    rw [F.deposited_flux hD,F.deposited_flux hab,F.deposited_flux ha,F.deposited_flux hend]
    abel
  rw [he]
  exact (F.deposited_posSemidef hk 0 a).add (F.deposited_posSemidef hk (a+L) D)

theorem selected_sqrt_aggregate (hk : 0≤k) {a L D : ℝ} (ha : 0≤a) (hL : 0≤L)
    (hend : a+L≤D) {n : ℕ} (hn : 0<n) :
    (∑ j:Fin n,Real.sqrt ((F.cellAbsorption a L n j).det.re))≤Real.sqrt (F.invariant D) := by
  exact posSemidef_sqrt_det_aggregate Finset.univ (F.cellAbsorption a L n) (fluxDefect (F.field D))
    (fun j _=>F.deposited_posSemidef hk _ _) (F.selected_rest_posSemidef hk ha hL hend hn)

theorem resource_cell_bounds {P Q a L : ℝ} {n : ℕ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q)
    (hL : 0≤L) (hn : 0<n) (hp : ∀ z∈Ioo a (a+L),F.p z≤P)
    (hq : ∀ z∈Ioo a (a+L),0≤F.q z ∧ F.q z≤Q)
    (hwidth : L/(n:ℝ)≤Real.pi/(k*Real.sqrt P)) :
    ∀ j:Fin n,Q/P*ResourceScalar.g (resourceCellU F.q a L (k*Real.sqrt P) Q n j)≤
      Real.sqrt ((F.cellAbsorption a L n j).det.re) := by
  intro j
  have hsub := resourceCell_subset_Ioo a hL hn j
  exact F.cell_sqrt_det_lower hk hP hQ (fun z hz=>hp z (hsub hz))
    (fun z hz=>hq z (hsub hz)) (resourceCellPoint_le_next a hL n j.val)
    (by simpa only [resourceCellPoint_step] using hwidth)

theorem resource_floor {P Q M a L D : ℝ} {n : ℕ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q)
    (ha : 0≤a) (hL : 0≤L) (hend : a+L≤D) (hn : 0<n)
    (hp : ∀ z∈Ioo a (a+L),F.p z≤P) (hq : ∀ z∈Ioo a (a+L),0≤F.q z ∧ F.q z≤Q)
    (hwidth : L/(n:ℝ)≤Real.pi/(k*Real.sqrt P))
    (hscalar : (n:ℝ)*ResourceScalar.g (ResourceFloor.U k P Q M/n)≤
      ∑ j:Fin n,ResourceScalar.g (resourceCellU F.q a L (k*Real.sqrt P) Q n j)) :
    ResourceFloor.beta k P Q M n≤F.invariant D := by
  have hcell := F.resource_cell_bounds hk hP hQ hL hn hp hq hwidth
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _=>hcell j)
  rw [← Finset.mul_sum] at hs
  have hagg := F.selected_sqrt_aggregate hk.le ha hL hend hn
  have hsc := mul_le_mul_of_nonneg_left hscalar (div_nonneg hQ.le hP.le)
  have hb : Q/P*(n:ℝ)*ResourceScalar.g (ResourceFloor.U k P Q M/n)≤Real.sqrt (F.invariant D) := by
    simpa only [mul_assoc] using hsc.trans (hs.trans hagg)
  have hnneg : 0≤Q/P*(n:ℝ)*ResourceScalar.g (ResourceFloor.U k P Q M/n) :=
    mul_nonneg (mul_nonneg (div_nonneg hQ.le hP.le) (Nat.cast_nonneg n)) (ResourceScalar.g_nonneg _)
  have hD : 0≤D := by linarith
  have hinv : 0≤F.invariant D := (Complex.nonneg_iff.mp (F.transfer_passive hk.le hD).det_nonneg).1
  have hsq := (sq_le_sq₀ hnneg (Real.sqrt_nonneg _)).mpr hb
  rw [Real.sq_sqrt hinv,← beta_eq_squared_scalar] at hsq
  exact hsq

def Selected (P Q M L D : ℝ) : Prop := ∃ a:ℝ,0≤a ∧ a+L≤D ∧
  (∀ z∈Ioo a (a+L),F.p z≤P) ∧
  (∀ z∈Ioo a (a+L),0≤F.q z ∧ F.q z≤Q) ∧ (∫ z in a..a+L,F.q z)=M

theorem half_floor {P Q M L D : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q) (hL : 0<L)
    (h : F.Selected P Q M L D) :
    ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L)≤F.invariant D := by
  obtain ⟨a,ha,hend,hp,hq,hmass⟩ := h
  let n := ResourceFloor.halfCellCount k P L
  have hn : 0<n := ResourceFloor.cellCount_pos _ _
  have hK : 0<k*Real.sqrt P := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hw := resourceCellWidth_half (L:=L) hk hP
  have hwidth : k*Real.sqrt P*(L/(n:ℝ))≤Real.pi/2 := by
    have hb := (le_div_iff₀ (show 0<2*k*Real.sqrt P by positivity)).mp hw
    dsimp [n]
    nlinarith
  have hwfull : L/(n:ℝ)≤Real.pi/(k*Real.sqrt P) := by
    apply (le_div_iff₀ hK).mpr
    nlinarith [Real.pi_pos]
  have hu := resourceCellU_bounds_Ioo hL.le hn hK hQ F.loss_integrable hq hwidth
  have hs := resourceCellU_sum F.q a L (k*Real.sqrt P) Q hn F.loss_integrable
  rw [hmass] at hs
  have hscalar := ResourceScalar.sum_g_half hn (resourceCellU F.q a L (k*Real.sqrt P) Q n) hu
  rw [hs] at hscalar
  exact F.resource_floor hk hP hQ ha hL.le hend hn hp hq hwfull hscalar

theorem full_floor {P Q M L D : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q) (hM : 0<M) (hL : 0<L)
    (h : F.Selected P Q M L D)
    (hcase : ResourceFloor.U k P Q M≤Real.pi/2 ∨
      ResourceFloor.U k P Q M/(ResourceFloor.fullCellCount k P L:ℝ)≤1/3) :
    ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L)≤F.invariant D := by
  obtain ⟨a,ha,hend,hp,hq,hmass⟩ := h
  let n := ResourceFloor.fullCellCount k P L
  have hn : 0<n := ResourceFloor.cellCount_pos _ _
  have hK : 0<k*Real.sqrt P := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hw := resourceCellWidth_full (L:=L) hk hP
  have hwidth : k*Real.sqrt P*(L/(n:ℝ))≤Real.pi := by
    have hb := (le_div_iff₀ hK).mp hw
    simpa only [mul_comm] using hb
  have hu := resourceCellU_bounds_Ioo hL.le hn hK hQ F.loss_integrable hq hwidth
  have hs := resourceCellU_sum F.q a L (k*Real.sqrt P) Q hn F.loss_integrable
  rw [hmass] at hs
  change (∑ j:Fin n,resourceCellU F.q a L (k*Real.sqrt P) Q n j)=ResourceFloor.U k P Q M at hs
  have hscalar := ResourceScalar.sum_g_full_cases hn (resourceCellU F.q a L (k*Real.sqrt P) Q n) hu
    (by rw [hs];exact ResourceFloor.U_pos hk hP hQ hM) (by rw [hs];exact hcase)
  rw [hs] at hscalar
  exact F.resource_floor hk hP hQ ha hL.le hend hn hp hq hw hscalar

/-- Original finite inequalities (27),(28), including the explicit strictly
positive estimate, without any lower bound on real permittivity. -/
theorem theorem45_finite {P Q M L D : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q)
    (hM : 0<M) (hL : 0<L) (h : F.Selected P Q M L D) :
    ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L)≤F.invariant D ∧
    4*k^4*M^4/(3*Q^2*(Real.pi+2*k*Real.sqrt P*L)^2)≤
      ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) ∧
    0<4*k^4*M^4/(3*Q^2*(Real.pi+2*k*Real.sqrt P*L)^2) ∧
    ((ResourceFloor.U k P Q M≤Real.pi/2 ∨
      ResourceFloor.U k P Q M/(ResourceFloor.fullCellCount k P L:ℝ)≤1/3) →
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L)≤F.invariant D) := by
  have hb : M≤Q*L := by
    obtain ⟨a,_,_,_,hq,hm⟩ := h
    rw [← hm]
    exact resourceMass_le_cap_Ioo hL.le F.loss_integrable hq
  exact ⟨F.half_floor hk hP hQ hL h,ResourceFloor.half_floor_explicit hk hP hQ hM hL hb,
    ResourceFloor.explicit_floor_pos hk hP hQ hM hL,F.full_floor hk hP hQ hM hL h⟩

theorem full_floor_eventually {P Q M : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q) (hM : 0<M) :
    ∀ᶠ L:ℝ in atTop,∀ (F:Profile k) (D:ℝ),F.Selected P Q M L D →
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L)≤F.invariant D := by
  filter_upwards [eventually_gt_atTop (0:ℝ),ResourceFloor.full_mean_eventually_small hk hP hQ hM] with L hL hs
  intro F D h
  exact F.full_floor hk hP hQ hM hL h (Or.inr hs)

theorem theorem45_uniform_asymptotic {P Q M : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q) (hM : 0<M)
    {ε:ℝ} (hε : 0<ε) :
    ∀ᶠ L:ℝ in atTop,∀ (F:Profile k) (D:ℝ),F.Selected P Q M L D →
      resourceAsymptoticCoefficient k P Q M-ε≤(k*L)^2*F.invariant D := by
  filter_upwards [resource_scaled_full_floor_eventually_lower hk hP hQ hM hε,
    full_floor_eventually hk hP hQ hM] with L hL hf
  intro F D h
  exact hL.trans (mul_le_mul_of_nonneg_left (hf F D h) (sq_nonneg _))

/-- The explicit finite floor with the original literal scattering invariant,
rather than an uninterpreted resource variable or assumed Gram determinant. -/
theorem theorem45_scattering_floor {P Q M L D : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q)
    (hM : 0<M) (hL : 0<L) (h : F.Selected P Q M L D) :
    4*k^4*M^4/(3*Q^2*(Real.pi+2*k*Real.sqrt P*L)^2)≤
      normalizedAbsorptionDet (transferReflectionLeft (waveTransfer (F.field D)))
        (transferReflectionRight (waveTransfer (F.field D)))
        (transferTransmissionRight (waveTransfer (F.field D))) := by
  have hD : 0≤D := by obtain ⟨a,ha,he,_⟩ := h; linarith
  rw [← F.invariant_scattering hk.le hD]
  have hf := F.theorem45_finite hk hP hQ hM hL h
  exact hf.2.1.trans hf.1

/-- Original (29) for every varying sequence of literal piecewise Helmholtz
profiles and selected intervals, including divergent scaled invariants. -/
theorem theorem45_sequence_lowerlimit {P Q M : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q) (hM : 0<M)
    (L D : ℕ→ℝ) (F : ℕ→Profile k) (hL : Tendsto L atTop atTop)
    (h : ∀ j,(F j).Selected P Q M (L j) (D j)) :
    (resourceAsymptoticCoefficient k P Q M:EReal)≤
      liminf (fun j=>((k*L j)^2*(F j).invariant (D j):EReal)) atTop := by
  have hf : ∀ᶠ j:ℕ in atTop,ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P (L j))≤
      (F j).invariant (D j) := by
    filter_upwards [hL.eventually (full_floor_eventually hk hP hQ hM)] with j hj
    exact hj (F j) (D j) (h j)
  exact resource_sequence_liminf_lower_of_floor hk hP hQ hM L
    (fun j=>(F j).invariant (D j)) hL hf

end GeneralizedResearch.HelmholtzProfile.Profile
