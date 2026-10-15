import GeneralizedResearch.HelmholtzProfile
import OQ7.FourierOpenCaps
import OQ7.ResourceScalar

/-! Derived modulus comparison and determinant floor for actual piecewise
Helmholtz profiles with arbitrary real permittivity, including negative and
zero values. The real cap and loss cap are imposed only on the selected cell. -/

noncomputable section
namespace GeneralizedResearch.HelmholtzProfile.Profile
open Set MeasureTheory OQ7
open scoped Matrix ComplexOrder Topology
variable {k : ℝ} (F : Profile k)

def fundamentalState (x : ℝ) : Fin 2→ℂ :=
  adjugate2 (F.field x) *ᵥ ![0,(Complex.I*(k:ℂ))⁻¹]
def fundamental (y x : ℝ) : ℂ := F.electric (F.fundamentalState x) y

theorem state_initial (x : ℝ) :
    F.field x *ᵥ F.fundamentalState x=![0,(Complex.I*(k:ℂ))⁻¹] := by
  rw [fundamentalState,Matrix.mulVec_mulVec,mul_adjugate2,F.field_det,one_smul,Matrix.one_mulVec]
theorem fundamental_initial (x : ℝ) : F.fundamental x x=0 := by
  have h := congrFun (F.state_initial x) 0
  simpa [fundamental,electric,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h
theorem fundamental_magnetic_initial (x : ℝ) :
    F.magnetic (F.fundamentalState x) x=(Complex.I*(k:ℂ))⁻¹ := by
  have h := congrFun (F.state_initial x) 1
  simpa [magnetic,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h

theorem fundamental_formula (y x : ℝ) :
    F.fundamental y x=(F.field y*adjugate2 (F.field x)) 0 1/(Complex.I*(k:ℂ)) := by
  simp [fundamental,electric,fundamentalState,Matrix.mulVec,dotProduct,
    Matrix.mul_apply,Fin.sum_univ_two,div_eq_mul_inv]
  ring

theorem modulus_comparison {P x h : ℝ} (hk : 0<k) (hP : 0<P)
    (hh : 0≤h) (hmax : h≤Real.pi/(k*Real.sqrt P))
    (hlocal : ∀ z∈Ioo x (x+h),F.p z≤P) :
    Real.sin (k*Real.sqrt P*h)/(k*Real.sqrt P)≤‖F.fundamental (x+h) x‖ := by
  classical
  rcases hh.eq_or_lt with hh|hh
  · rw [← hh]
    simp [F.fundamental_initial]
  let v := F.fundamentalState x
  let s := fun t : ℝ=>F.fundamental (x+t) x
  let ds := fun t : ℝ=>Complex.I*(k:ℂ)*F.magnetic v (x+t)
  let p := fun t : ℝ=>F.p (x+t)
  let q := fun t : ℝ=>F.q (x+t)
  let bad := F.interfaces.image (fun z=>z-x)
  have hK : 0<k*Real.sqrt P := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hKh : k*Real.sqrt P*h≤Real.pi := by
    simpa only [mul_comm] using (le_div_iff₀ hK).mp hmax
  have hscont : Continuous s := (F.electric_continuous v).comp (continuous_const.add continuous_id)
  have hdscont : Continuous ds := ((F.magnetic_continuous v).comp
    (continuous_const.add continuous_id)).const_mul _
  have hsderiv (t : ℝ) : HasDerivAt s (ds t) t := by
    convert (F.electric_hasDerivAt v (x+t)).scomp t ((hasDerivAt_id t).const_add x) using 1 <;>
      simp [s,ds,v,fundamental,Function.comp_def]
  have hdsderiv (t : ℝ) (_ht : t∈Ioo 0 h) (htbad : t∉bad) :
      HasDerivAt ds (-(k:ℂ)^2*((p t:ℂ)+Complex.I*(q t:ℂ))*s t) t := by
    have hx : x+t∉F.interfaces := by
      intro hz
      exact htbad (Finset.mem_image.mpr ⟨x+t,hz,by ring⟩)
    have hd := ((F.magnetic_hasDerivAt v (x+t) hx).scomp t
      ((hasDerivAt_id t).const_add x)).const_mul (Complex.I*(k:ℂ))
    convert hd using 1
    · rfl
    · dsimp [ds,s,p,q,fundamental,v]
      ring_nf
      simp [Complex.I_sq]
      ring
  have hcap (t : ℝ) (ht : t∈Ioo 0 h) : k^2*p t≤(k*Real.sqrt P)^2 := by
    have hp := hlocal (x+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simpa only [mul_pow,Real.sq_sqrt hP.le] using mul_le_mul_of_nonneg_left hp (sq_nonneg k)
  have hs0 : s 0=0 := by simpa [s] using F.fundamental_initial x
  have hds0 : ds 0=1 := by
    have hkn : Complex.I*(k:ℂ)≠0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk.ne')
    dsimp [ds,v]
    rw [add_zero,F.fundamental_magnetic_initial,mul_inv_cancel₀ hkn]
  exact ModulusComparison.helmholtz_modulus_comparison hK hh hKh bad hscont hdscont
    hsderiv hdsderiv hcap hs0 hds0

theorem cell_comparison {P a b : ℝ} (hk : 0<k) (hP : 0<P)
    (hlength : b-a≤Real.pi/(k*Real.sqrt P)) (hp : ∀ z∈Ioo a b,F.p z≤P) :
    ∀ x∈Icc a b,∀ y∈Icc a b,x≤y →
      Real.sin (k*Real.sqrt P*(y-x))/(k*Real.sqrt P)≤‖F.fundamental y x‖ := by
  intro x hx y hy hxy
  have hw : y-x≤Real.pi/(k*Real.sqrt P) := by linarith [hx.1,hy.2]
  have h := F.modulus_comparison (x:=x) (h:=y-x) hk hP (sub_nonneg.mpr hxy) hw
    (fun z hz=>hp z ⟨by linarith [hx.1,hz.1],by linarith [hy.2,hz.2]⟩)
  simpa only [add_sub_cancel] using h

def pairKernel (p : ℝ×ℝ) : ℝ := F.q p.1*F.q p.2*Complex.normSq (F.fundamental p.2 p.1)

theorem wedge_normSq (hk : k≠0) (x y : ℝ) :
    Complex.normSq (F.field x 0 0*F.field y 0 1-F.field x 0 1*F.field y 0 0)=
      k^2*Complex.normSq (F.fundamental y x) := by
  have h := matrixElectricWedge (F.field x) (F.field y) 1
  simp only [mul_one,Matrix.det_one,one_mul] at h
  rw [h,F.fundamental_formula,Complex.normSq_div,Complex.normSq_mul,
    Complex.normSq_I,Complex.normSq_ofReal,one_mul]
  field_simp [hk]

theorem gramPair_eq (hk : k≠0) (p : ℝ×ℝ) :
    gramPairKernel F.q (fun x j=>F.field x 0 j) p=k^2*F.pairKernel p := by
  unfold gramPairKernel pairKernel
  rw [F.wedge_normSq hk]
  ring

theorem pair_integrable (hk : k≠0) (a b : ℝ) :
    Integrable F.pairKernel ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
  have hg := gramPairKernel_integrable (volume.restrict (Ioc a b)) F.q
    (fun x j=>F.field x 0 j) (fun i j=>(F.weighted_entry_integrable i j a b).1)
  have he : (fun p=>(k^2)⁻¹*gramPairKernel F.q (fun x j=>F.field x 0 j) p)=F.pairKernel := by
    funext p
    rw [F.gramPair_eq hk]
    field_simp [hk]
  rw [← he]
  exact hg.const_mul _

/-- Exact normalized Gram determinant, derived in a fundamental-field basis.
Its total is precisely det(I−S†S)/|t|² by `invariant_scattering`. -/
theorem deposited_det (hk : k≠0) (a b : ℝ) :
    (F.deposited a b).det.re=4*k^4*∫ p in {p:ℝ×ℝ|p.1<p.2},F.pairKernel p
      ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) := by
  have hg := weightedGram_det_triangleIntegral (volume.restrict (Ioc a b)) F.q
    (fun x j=>F.field x 0 j) (fun i j=>(F.weighted_entry_integrable i j a b).1)
  rw [funext (F.gramPair_eq hk),integral_const_mul] at hg
  have he : (F.deposited a b).det=
      ((4*k^4*∫ p in {p:ℝ×ℝ|p.1<p.2},F.pairKernel p
        ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)):ℝ):ℂ) := by
    rw [deposited,Matrix.det_smul,hg]
    simp only [Fintype.card_fin]
    push_cast
    ring
  exact_mod_cast congrArg Complex.re he

theorem pair_sine_lower {K a b x y : ℝ} (hK : 0<K) (hlength : b-a≤Real.pi/K)
    (hcomp : ∀ x∈Icc a b,∀ y∈Icc a b,x≤y →Real.sin (K*(y-x))/K≤‖F.fundamental y x‖)
    (hx : x∈Icc a b) (hy : y∈Icc a b) (hxy : x≤y) :
    F.q x*F.q y*Real.sin (K*(y-x))^2/K^2≤F.pairKernel (x,y) := by
  have hθ0 : 0≤K*(y-x) := mul_nonneg hK.le (sub_nonneg.mpr hxy)
  have hθπ : K*(y-x)≤Real.pi := by
    have hd : y-x≤b-a := by linarith [hx.1,hy.2]
    calc
      _ ≤ K*(b-a) := mul_le_mul_of_nonneg_left hd hK.le
      _ ≤ K*(Real.pi/K) := mul_le_mul_of_nonneg_left hlength hK.le
      _ = Real.pi := mul_div_cancel₀ _ hK.ne'
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hn := (sq_le_sq₀ (div_nonneg hsin hK.le) (norm_nonneg _)).mpr (hcomp x hx y hy hxy)
  rw [div_pow,← Complex.normSq_eq_norm_sq] at hn
  simpa only [pairKernel,mul_div_assoc] using
    mul_le_mul_of_nonneg_left hn (mul_nonneg (F.passive x) (F.passive y))

theorem cell_pair_lower {Q K a b : ℝ} (hk : 0<k) (hQ : 0<Q) (hK : 0<K)
    (hcap : ∀ z∈Ioo a b,0≤F.q z ∧ F.q z≤Q) (hab : a≤b) (hlength : b-a≤Real.pi/K)
    (hcomp : ∀ x∈Icc a b,∀ y∈Icc a b,x≤y →Real.sin (K*(y-x))/K≤‖F.fundamental y x‖) :
    (Q^2/(4*K^2)*ResourceScalar.f (K*(∫ z in a..b,F.q z)/Q))/K^2≤
      ∫ p in {p:ℝ×ℝ|p.1<p.2},F.pairKernel p
        ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) := by
  let μ := volume.restrict (Ioc a b)
  let low : ℝ×ℝ→ℝ := fun p=>F.q p.1*F.q p.2*Real.sin (K*(p.2-p.1))^2
  let triangle : Set (ℝ×ℝ) := {p|p.1<p.2}
  have htri : MeasurableSet triangle := (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hlo : Integrable low (μ.prod μ) := sineSquare_product_integrable (F.loss_integrable a b)
  have hhi := F.pair_integrable hk.ne' a b
  have hs : ∀ᵐ p ∂μ.prod μ,p.1∈Ioc a b ∧ p.2∈Ioc a b := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hm : (∫ p in triangle,low p/K^2 ∂μ.prod μ)≤∫ p in triangle,F.pairKernel p ∂μ.prod μ := by
    apply setIntegral_mono_on_ae (hlo.div_const (K^2)).integrableOn hhi.integrableOn htri
    filter_upwards [hs] with p hp
    intro hpt
    exact F.pair_sine_lower hK hlength hcomp (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2) hpt.le
  rw [integral_div] at hm
  have hf := sineSquare_triangleIntegral_capped_Ioo hab hK hQ hlength (F.loss_integrable a b) hcap
  exact (div_le_div_of_nonneg_right hf (sq_nonneg K)).trans hm

theorem cell_det_lower {P Q a b : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q)
    (hp : ∀ z∈Ioo a b,F.p z≤P) (hq : ∀ z∈Ioo a b,0≤F.q z ∧ F.q z≤Q)
    (hab : a≤b) (hlength : b-a≤Real.pi/(k*Real.sqrt P)) :
    Q^2/P^2*ResourceScalar.f (k*Real.sqrt P*(∫ z in a..b,F.q z)/Q)≤(F.deposited a b).det.re := by
  let K := k*Real.sqrt P
  have hK : 0<K := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hKsq : K^2=k^2*P := by dsimp [K]; rw [mul_pow,Real.sq_sqrt hP.le]
  have hl := F.cell_pair_lower hk hQ hK hq hab hlength (F.cell_comparison hk hP hlength hp)
  rw [F.deposited_det hk.ne']
  have hm := mul_le_mul_of_nonneg_left hl (show 0≤4*k^4 by positivity)
  have he : 4*k^4*((Q^2/(4*K^2)*ResourceScalar.f (K*(∫ z in a..b,F.q z)/Q))/K^2)=
      Q^2/P^2*ResourceScalar.f (K*(∫ z in a..b,F.q z)/Q) := by
    calc
      _ = k^4*Q^2/(K^2)^2*ResourceScalar.f (K*(∫ z in a..b,F.q z)/Q) := by field_simp
      _ = _ := by rw [hKsq]; field_simp
  rwa [he] at hm

theorem cell_sqrt_det_lower {P Q a b : ℝ} (hk : 0<k) (hP : 0<P) (hQ : 0<Q)
    (hp : ∀ z∈Ioo a b,F.p z≤P) (hq : ∀ z∈Ioo a b,0≤F.q z ∧ F.q z≤Q)
    (hab : a≤b) (hlength : b-a≤Real.pi/(k*Real.sqrt P)) :
    Q/P*ResourceScalar.g (k*Real.sqrt P*(∫ z in a..b,F.q z)/Q)≤Real.sqrt ((F.deposited a b).det.re) := by
  have h := Real.sqrt_le_sqrt (F.cell_det_lower hk hP hQ hp hq hab hlength)
  rw [show Q^2/P^2=(Q/P)^2 by rw [div_pow],Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (div_nonneg hQ.le hP.le)] at h
  exact h

end GeneralizedResearch.HelmholtzProfile.Profile
