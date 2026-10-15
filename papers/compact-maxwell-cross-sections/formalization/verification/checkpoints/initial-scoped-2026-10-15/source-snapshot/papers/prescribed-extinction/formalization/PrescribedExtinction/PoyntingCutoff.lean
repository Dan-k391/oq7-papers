import PrescribedExtinction.SmoothOutgoingFields
import PrescribedExtinction.VolumeScatteringBridge
import PrescribedExtinction.TensorLossCoercivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

def vectorConjugate (v : Vector) : Vector := WithLp.toLp 2 (fun i => star (v i))

theorem vectorConjugate_apply (v : Vector) (i : Fin 3) : vectorConjugate v i = star (v i) := rfl

theorem vectorConjugate_contDiff (F : Field) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => vectorConjugate (F x)) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  exact Complex.conjCLE.contDiff.comp ((vectorCoordinate i).contDiff.comp hF)

theorem vectorConjugate_component_fderiv (F : Field) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (i j : Fin 3) (x : Position) :
    fderiv ℝ (fun y => vectorConjugate (F y)) x (basisR j) i =
      star (fderiv ℝ F x (basisR j) i) := by
  have hc := (vectorCoordinate i).hasFDerivAt.comp x
    (hF.differentiable (by simp) x).hasFDerivAt
  have hconj := Complex.conjCLE.hasFDerivAt.comp x hc
  have hvec := (vectorCoordinate i).hasFDerivAt.comp x
    ((vectorConjugate_contDiff F hF).differentiable (by simp) x).hasFDerivAt
  have hid : (fun y => vectorCoordinate i (vectorConjugate (F y))) =
      (fun y => Complex.conjCLE (vectorCoordinate i (F y))) := rfl
  change HasFDerivAt (fun y => vectorCoordinate i (vectorConjugate (F y))) _ x at hvec
  rw [hid] at hvec
  have he := hvec.unique hconj
  exact congrArg (fun D : Position →L[ℝ] ℂ => D (basisR j)) he

theorem curl_vectorConjugate (F : Field) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    curl (fun x => vectorConjugate (F x)) = fun x => vectorConjugate (curl F x) := by
  funext x
  ext i
  fin_cases i <;>
    simp [curl, vectorConjugate_apply, vectorConjugate_component_fderiv F hF]

def scalarGradient (ψ : Position → ℝ) (x : Position) : Position :=
  WithLp.toLp 2 (fun j => fderiv ℝ ψ x (basisR j))

theorem curl_real_smul (ψ : Position → ℝ) (F : Field)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Position) :
    curl (fun y => ψ y • F y) x =
      cross (complexify (scalarGradient ψ x)) (F x) + ψ x • curl F x := by
  have hd := ((hψ.differentiable (by simp) x).hasFDerivAt.smul
    (hF.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => ψ y • F y) x = _ at hd
  ext i
  fin_cases i <;>
    simp [curl, hd, scalarGradient, complexify, cross, PiLp.add_apply, PiLp.smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.real_smul] <;> ring

theorem bilinear_cross_conjugate (H E : Vector) (v : Position) :
    bilinear H (cross (complexify v) (vectorConjugate E)) =
      pairing E (cross H (complexify v)) := by
  simp [bilinear, pairing, cross, complexify, vectorConjugate, Fin.sum_univ_three]
  ring

theorem bilinear_add_right (u v w : Vector) : bilinear u (v + w) = bilinear u v + bilinear u w := by
  simp [bilinear, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

theorem bilinear_complex_smul_right (u v : Vector) (z : ℂ) :
    bilinear u (z • v) = z * bilinear u v := by
  simp [bilinear, PiLp.smul_apply, Finset.mul_sum, mul_left_comm]

theorem bilinear_real_smul_right (u v : Vector) (r : ℝ) :
    bilinear u (r • v) = (r : ℂ) * bilinear u v := by
  simp [bilinear, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum, mul_left_comm]

theorem bilinear_vectorConjugate_right (u v : Vector) :
    bilinear u (vectorConjugate v) = pairing v u := by
  simp [bilinear, pairing, vectorConjugate_apply, mul_comm]

theorem vectorConjugate_smul (z : ℂ) (v : Vector) :
    vectorConjugate (z • v) = star z • vectorConjugate v := by
  ext i
  simp [vectorConjugate_apply, PiLp.smul_apply]

theorem cutoff_curl_pairing_real (ψ : Position → ℝ) (E H : Field) (k : ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hE : ContDiff ℝ (⊤ : ℕ∞) E)
    (hcurl : curl E = fun x => (Complex.I * (k : ℂ)) • H x) (x : Position) :
    (bilinear (H x) (curl (fun y => ψ y • vectorConjugate (E y)) x)).re =
      (pairing (E x) (cross (H x) (complexify (scalarGradient ψ x)))).re := by
  rw [curl_real_smul ψ _ hψ (vectorConjugate_contDiff E hE),
    bilinear_add_right, bilinear_cross_conjugate, bilinear_real_smul_right,
    curl_vectorConjugate E hE]
  dsimp only
  rw [congrFun hcurl x, vectorConjugate_smul,
    bilinear_complex_smul_right, bilinear_vectorConjugate_right, pairing_self]
  simp [Complex.mul_re, Complex.mul_im]

theorem cutoff_source_pairing_real (ψ : Position → ℝ) (E H p : Field) (k : ℝ)
    (hcurl : curl H = fun x => (-Complex.I * (k : ℂ)) • (E x + p x)) (x : Position) :
    (bilinear (curl H x) (ψ x • vectorConjugate (E x))).re =
      -k * ((ψ x : ℂ) * pairing (p x) (E x)).im := by
  rw [congrFun hcurl x, bilinear_real_smul_right, bilinear_vectorConjugate_right, pairing_eq_inner,
    inner_smul_right, inner_add_right]
  have hi := inner_im_symm (𝕜 := ℂ) (E x) (p x)
  change (inner ℂ (E x) (p x)).im = -(inner ℂ (p x) (E x)).im at hi
  have hz : (inner ℂ (E x) (E x)).im = 0 := inner_self_im (𝕜 := ℂ) (E x)
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, zero_mul, zero_add, one_mul, neg_mul,
    mul_zero, sub_zero, pairing_eq_inner, hz, hi]
  ring

theorem compact_scalar_weight_integrable (ψ : Position → ℝ) (hψ : Continuous ψ)
    (hs : HasCompactSupport ψ) (f : Position → ℂ) (hf : Continuous f) :
    Integrable (fun x => (ψ x : ℂ) * f x) volume := by
  have hc : Continuous (ψ • f) := hψ.smul hf
  have hcs : HasCompactSupport (ψ • f) := HasCompactSupport.smul_right (f' := f) hs
  have h : Integrable (ψ • f) (volume : Measure Position) :=
    hc.integrable_of_hasCompactSupport hcs
  exact h.congr (ae_of_all _ fun x => by simp [Complex.real_smul])

/-- Exact compact-cutoff source Poynting identity. All terms are genuine
integrals of the fields and current; no power balance is assumed. -/
theorem smooth_source_cutoff_energy (k : ℝ) (E H p : Field)
    (hE : ContDiff ℝ (⊤ : ℕ∞) E) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hp : Continuous p)
    (he : curl E = fun x => (Complex.I * (k : ℂ)) • H x)
    (hh : curl H = fun x => (-Complex.I * (k : ℂ)) • (E x + p x))
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    k * (∫ x : Position, (ψ x : ℂ) * pairing (p x) (E x)).im =
      -(∫ x : Position, (pairing (E x) (cross (H x) (complexify (scalarGradient ψ x)))).re) := by
  let φ : Field := ψ • (fun x => vectorConjugate (E x))
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.smul (vectorConjugate_contDiff E hE)
  have hsφ : HasCompactSupport φ := HasCompactSupport.smul_right
    (f' := fun x => vectorConjugate (E x)) hs
  have hleft := compactField_bilinear_integrable H hH.continuous.locallyIntegrable
    (curl φ) (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hright := compactField_bilinear_integrable (curl H)
    (smoothField_curl_contDiff H hH).continuous.locallyIntegrable φ hφ.continuous hsφ
  have h := congrArg Complex.re (smoothField_hasWeakCurl H hH φ hφ hsφ)
  change RCLike.re (∫ x : Position, bilinear (H x) (curl φ x)) =
    RCLike.re (∫ x : Position, bilinear (curl H x) (φ x)) at h
  rw [← integral_re hleft, ← integral_re hright] at h
  change (∫ x : Position, (bilinear (H x) (curl φ x)).re) =
    (∫ x : Position, (bilinear (curl H x) (φ x)).re) at h
  have hl : (∫ x : Position, (bilinear (H x) (curl φ x)).re) =
      ∫ x : Position, (pairing (E x) (cross (H x) (complexify (scalarGradient ψ x)))).re := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => cutoff_curl_pairing_real ψ E H k hψ hE he x
  have hwork := compact_scalar_weight_integrable ψ hψ.continuous hs
    (fun x => pairing (p x) (E x)) (by simpa only [pairing_eq_inner] using hp.inner hE.continuous)
  have hr : (∫ x : Position, (bilinear (curl H x) (φ x)).re) =
      -k * (∫ x : Position, (ψ x : ℂ) * pairing (p x) (E x)).im := by
    change (∫ x : Position, (bilinear (curl H x) (φ x)).re) =
      -k * RCLike.im (∫ x : Position, (ψ x : ℂ) * pairing (p x) (E x))
    rw [← integral_im hwork, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => cutoff_source_pairing_real ψ E H p k hh x
  rw [hl, hr] at h
  linarith

theorem smoothPhysicalSource_cutoff_energy (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    k * (∫ x : Position, (ψ x : ℂ) * pairing (p.current x) (smoothElectricSource k p x)).im =
      -(∫ x : Position, (pairing (smoothElectricSource k p x)
        (cross (smoothMagneticSource k p x) (complexify (scalarGradient ψ x)))).re) :=
  smooth_source_cutoff_energy k _ _ _ (smoothElectricSource_contDiff k p hp)
    (smoothMagneticSource_contDiff k p hp) hp.continuous (smoothElectricSource_curl k p hp)
    (smoothMagneticSource_curl k p hp) ψ hψ hs

end OQ7Prescribed
