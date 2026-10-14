import PrescribedExtinction.WeakCurlBridge
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem smoothScalar_distributionPartial (f : Position → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    distributionPartial j (Distribution.ofFun ⊤ f volume ⊤) =
      Distribution.ofFun ⊤ (fun x => fderiv ℝ f x (basisR j)) volume ⊤ := by
  have hc : Continuous (fun x : Position => fderiv ℝ f x (basisR j)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hl : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hld : LocallyIntegrable (fun x : Position => fderiv ℝ f x (basisR j)) volume := hc.locallyIntegrable
  ext φ
  have h0 := φ.integrable_smul (hl.locallyIntegrableOn ⊤)
  have h1 := (testPartial j φ).integrable_smul (hl.locallyIntegrableOn ⊤)
  have h2 := φ.integrable_smul (hld.locallyIntegrableOn ⊤)
  have hid : (fun x : Position => fderiv ℝ φ x (basisR j) • f x) =
      (fun x => testPartial j φ x • f x) := by
    funext x
    rw [testPartial_eq_fderiv]
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := (volume : Measure Position)) (v := basisR j) (hid.symm ▸ h1) h2 h0
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  rw [distributionPartial, Distribution.lineDerivCLM_apply,
    Distribution.ofFun_apply (hl.locallyIntegrableOn ⊤),
    Distribution.ofFun_apply (hld.locallyIntegrableOn ⊤)]
  change -(∫ x : Position, testPartial j φ x • f x) = _
  rw [hid] at h
  exact h.symm

theorem planePhase_contDiff (k : ℝ) (σ : Direction) :
    ContDiff ℝ (⊤ : ℕ∞) (planePhase k σ) := by
  unfold planePhase
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position => x 2) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Position →L[ℝ] ℝ).contDiff
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position => σ.sign * k * x 2) :=
    contDiff_const.mul hproj
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hr)).cexp

theorem planePhase_hasFDerivAt (k : ℝ) (σ : Direction) (x : Position) :
    HasFDerivAt (planePhase k σ)
      ((Complex.I * ((σ.sign * k : ℝ) : ℂ) * planePhase k σ x) •
        (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2))) x := by
  have h := (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Position →L[ℝ] ℝ)).hasFDerivAt (x := x)
  have he := (h.const_mul (Complex.I * ((σ.sign * k : ℝ) : ℂ))).cexp
  convert he using 1
  · funext y
    simp [planePhase, mul_assoc]
  · ext y
    simp [planePhase, mul_assoc, PiLp.proj_apply]
    ring

theorem incidentMagnetic_eq (k : ℝ) (σ : Direction) :
    incidentMagnetic k σ = fun x => (-(σ.sign : ℂ) * planePhase k σ x) • basisC 0 := by
  funext x
  ext i
  fin_cases i <;> simp [incidentMagnetic, incidentElectric, cross, basisC, PiLp.smul_apply]

theorem incidentElectric_contDiff (k : ℝ) (σ : Direction) :
    ContDiff ℝ (⊤ : ℕ∞) (incidentElectric k σ) :=
  (planePhase_contDiff k σ).smul contDiff_const

theorem incidentMagnetic_contDiff (k : ℝ) (σ : Direction) :
    ContDiff ℝ (⊤ : ℕ∞) (incidentMagnetic k σ) := by
  rw [incidentMagnetic_eq]
  exact (contDiff_const.mul (planePhase_contDiff k σ)).smul contDiff_const

theorem incidentElectric_curl (k : ℝ) (σ : Direction) (x : Position) :
    curl (incidentElectric k σ) x = (Complex.I * (k : ℂ)) • incidentMagnetic k σ x := by
  have h := (planePhase_hasFDerivAt k σ x).smul_const (basisC 1)
  change HasFDerivAt (incidentElectric k σ) _ x at h
  ext i
  fin_cases i <;> simp [curl, h.fderiv, incidentMagnetic_eq, basisR, basisC,
    PiLp.smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply] <;> ring

theorem incidentMagnetic_curl (k : ℝ) (σ : Direction) (x : Position) :
    curl (incidentMagnetic k σ) x = (-Complex.I * (k : ℂ)) • incidentElectric k σ x := by
  have h := ((planePhase_hasFDerivAt k σ x).const_mul (-(σ.sign : ℂ))).smul_const (basisC 0)
  rw [← incidentMagnetic_eq] at h
  ext i
  cases σ <;> fin_cases i <;> simp [curl, h.fderiv, incidentElectric, basisR, basisC,
    PiLp.smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, Direction.sign] <;> ring

theorem smoothField_curl_continuous (F : Field) (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (curl F) := by
  have hc : Continuous (fun x : Position => fderiv ℝ F x) := hf.continuous_fderiv (by simp)
  have hj (j i : Fin 3) : Continuous (fun x : Position => fderiv ℝ F x (basisR j) i) :=
    (vectorCoordinate i).continuous.comp (hc.clm_apply continuous_const)
  unfold curl
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (hj 1 2).sub (hj 2 1)
  · exact (hj 2 0).sub (hj 0 2)
  · exact (hj 0 1).sub (hj 1 0)

theorem smoothField_component_partial (F : Field) (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (i j : Fin 3) :
    distributionPartial j (fieldComponentDistribution F i) =
      Distribution.ofFun ⊤ (fun x => fderiv ℝ F x (basisR j) i) volume ⊤ := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position => F x i) :=
    (vectorCoordinate i).contDiff.comp hf
  rw [fieldComponentDistribution, smoothScalar_distributionPartial _ hc]
  congr 1
  funext x
  exact congrArg (fun D : Position →L[ℝ] ℂ => D (basisR j))
    ((vectorCoordinate i).hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv

theorem smoothField_distributionCurl (F : Field) (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    distributionCurl (fieldComponentDistribution F) = fieldComponentDistribution (curl F) := by
  have hl (j i : Fin 3) : LocallyIntegrable (fun x : Position => fderiv ℝ F x (basisR j) i) volume :=
    ((vectorCoordinate i).continuous.comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)).locallyIntegrable
  funext i
  fin_cases i <;> simp [distributionCurl, smoothField_component_partial F hf]
  all_goals
    ext φ
    rw [sub_apply, Distribution.ofFun_apply ((hl _ _).locallyIntegrableOn _),
      Distribution.ofFun_apply ((hl _ _).locallyIntegrableOn _),
      fieldComponentDistribution_apply _ (smoothField_curl_continuous F hf).locallyIntegrable,
      ← integral_sub (φ.integrable_smul ((hl _ _).locallyIntegrableOn _))
        (φ.integrable_smul ((hl _ _).locallyIntegrableOn _))]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp [curl, Complex.real_smul]; ring

theorem smoothField_hasWeakCurl (F : Field) (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    HasWeakCurl F (curl F) :=
  distributionCurl_eq_implies_hasWeakCurl _ _ hf.continuous.locallyIntegrable
    (smoothField_curl_continuous F hf).locallyIntegrable (smoothField_distributionCurl F hf)

theorem incidentElectric_first_weakCurl (k : ℝ) (σ : Direction) :
    HasWeakCurl (incidentElectric k σ) (fun x => (Complex.I * (k : ℂ)) • incidentMagnetic k σ x) := by
  convert smoothField_hasWeakCurl _ (incidentElectric_contDiff k σ) using 1
  exact (funext (incidentElectric_curl k σ)).symm

theorem incidentMagnetic_second_weakCurl (k : ℝ) (σ : Direction) :
    HasWeakCurl (incidentMagnetic k σ) (fun x => (-Complex.I * (k : ℂ)) • incidentElectric k σ x) := by
  convert smoothField_hasWeakCurl _ (incidentMagnetic_contDiff k σ) using 1
  exact (funext (incidentMagnetic_curl k σ)).symm

theorem incidentElectric_locallySquareIntegrable (k : ℝ) (σ : Direction) :
    LocallySquareIntegrable (incidentElectric k σ) := by
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply MemLp.of_bound ((incidentElectric_contDiff k σ).continuous.aestronglyMeasurable.restrict) 1
  exact ae_of_all _ fun x => by simp [incidentElectric, norm_smul, planePhase_norm, basisC]

theorem incidentMagnetic_locallySquareIntegrable (k : ℝ) (σ : Direction) :
    LocallySquareIntegrable (incidentMagnetic k σ) := by
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply MemLp.of_bound ((incidentMagnetic_contDiff k σ).continuous.aestronglyMeasurable.restrict) 1
  apply ae_of_all
  intro x
  cases σ <;> simp [incidentMagnetic_eq, norm_smul, planePhase_norm, basisC, Direction.sign]

end OQ7Prescribed
