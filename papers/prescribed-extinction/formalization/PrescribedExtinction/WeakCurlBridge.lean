import PrescribedExtinction.PhysicalSourceFields

/-! Bridge from the original continuous scalar distributions to all smooth
compact complex vector tests in the physical Maxwell definition. Every test
pairing and derivative pairing is proved integrable before rearrangement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

def complexRealTest (ψ : Position → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) (L : ℂ →L[ℝ] ℝ) : ScalarTest where
  toFun := fun x => L (ψ x)
  contDiff' := L.contDiff.comp hψ
  hasCompactSupport' := hs.comp_left L.map_zero
  tsupport_subset' := Set.subset_univ _

theorem complexRealTest_partial (ψ : Position → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) (L : ℂ →L[ℝ] ℝ) (j : Fin 3) (x : Position) :
    testPartial j (complexRealTest ψ hψ hs L) x = L (fderiv ℝ ψ x (basisR j)) := by
  rw [testPartial_eq_fderiv]
  change fderiv ℝ (L ∘ ψ) x (basisR j) = _
  exact congrArg (fun D : Position →L[ℝ] ℝ => D (basisR j))
    (L.hasFDerivAt.comp x (hψ.differentiable (by simp) x).hasFDerivAt).fderiv

def complexTestEval (T : ScalarDistribution) (ψ : Position → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) : ℂ :=
  T (complexRealTest ψ hψ hs Complex.reCLM) +
    Complex.I * T (complexRealTest ψ hψ hs Complex.imCLM)

theorem fieldComponent_locallyIntegrable (F : Field) (hF : LocallyIntegrable F volume)
    (i : Fin 3) : LocallyIntegrable (fun x => F x i) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (vectorCoordinate i).integrable_comp (hF.integrableOn_isCompact hK)

theorem compactTest_component_integrable (F : Field) (hF : LocallyIntegrable F volume)
    (i : Fin 3) (ψ : Position → ℂ) (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x => ψ x * F x i) volume := by
  exact (fieldComponent_locallyIntegrable F hF i).integrable_smul_left_of_hasCompactSupport hc hs

theorem complexTestEval_field (F : Field) (hF : LocallyIntegrable F volume)
    (i : Fin 3) (ψ : Position → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    complexTestEval (fieldComponentDistribution F i) ψ hψ hs =
      ∫ x : Position, ψ x * F x i := by
  have hr := compactTest_component_integrable F hF i _
    (Complex.ofRealCLM.continuous.comp (Complex.reCLM.continuous.comp hψ.continuous))
    ((hs.comp_left Complex.reCLM.map_zero).comp_left Complex.ofRealCLM.map_zero)
  have hi := compactTest_component_integrable F hF i _
    (Complex.ofRealCLM.continuous.comp (Complex.imCLM.continuous.comp hψ.continuous))
    ((hs.comp_left Complex.imCLM.map_zero).comp_left Complex.ofRealCLM.map_zero)
  change Integrable (fun x : Position => ((ψ x).re : ℂ) * F x i) volume at hr
  change Integrable (fun x : Position => ((ψ x).im : ℂ) * F x i) volume at hi
  rw [complexTestEval, fieldComponentDistribution_apply _ hF,
    fieldComponentDistribution_apply _ hF]
  change (∫ x : Position, ((ψ x).re : ℂ) * F x i) +
    Complex.I * (∫ x : Position, ((ψ x).im : ℂ) * F x i) = _
  rw [← integral_const_mul, ← integral_add hr (hi.const_mul _)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (ψ x).re * F x i + Complex.I * ((ψ x).im * F x i) = ψ x * F x i
    calc
      _ = (((ψ x).re : ℂ) + (ψ x).im * Complex.I) * F x i := by ring
      _ = _ := by rw [Complex.re_add_im]

theorem complexTestEval_partial_field (F : Field) (hF : LocallyIntegrable F volume)
    (i j : Fin 3) (ψ : Position → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    complexTestEval (distributionPartial j (fieldComponentDistribution F i)) ψ hψ hs =
      -(∫ x : Position, (fderiv ℝ ψ x (basisR j)) * F x i) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x (basisR j)) := by
    exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hs' := hs.fderiv_apply ℝ (basisR j)
  have he (L : ℂ →L[ℝ] ℝ) :
      testPartial j (complexRealTest ψ hψ hs L) =
        complexRealTest (fun x => fderiv ℝ ψ x (basisR j)) hd hs' L := by
    ext x
    exact complexRealTest_partial ψ hψ hs L j x
  simp only [complexTestEval, distributionPartial, Distribution.lineDerivCLM_apply]
  change -(fieldComponentDistribution F i (testPartial j (complexRealTest ψ hψ hs Complex.reCLM))) +
    Complex.I * -(fieldComponentDistribution F i (testPartial j (complexRealTest ψ hψ hs Complex.imCLM))) = _
  rw [he, he]
  rw [mul_neg, ← neg_add, ← complexTestEval, complexTestEval_field F hF]

theorem complexTestEval_sub (S T : ScalarDistribution) (ψ : Position → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    complexTestEval (S - T) ψ hψ hs =
      complexTestEval S ψ hψ hs - complexTestEval T ψ hψ hs := by
  simp only [complexTestEval, sub_apply]
  ring

theorem testComponent_fderiv (φ : Field) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i j : Fin 3) (x : Position) :
    fderiv ℝ (fun y => φ y i) x (basisR j) = (fderiv ℝ φ x (basisR j)) i := by
  let L : Vector →L[ℝ] ℂ := (vectorCoordinate i).restrictScalars ℝ
  exact congrArg (fun D : Position →L[ℝ] ℂ => D (basisR j))
    (L.hasFDerivAt.comp x (hφ.differentiable (by simp) x).hasFDerivAt).fderiv

theorem integral_three_sub (a b c d e f : Position → ℂ)
    (ha : Integrable a volume) (hb : Integrable b volume)
    (hc : Integrable c volume) (hd : Integrable d volume)
    (he : Integrable e volume) (hf : Integrable f volume) :
    (∫ x : Position, (a x - b x) + (c x - d x) + (e x - f x)) =
      ((∫ x : Position, a x) - ∫ x : Position, b x) +
      ((∫ x : Position, c x) - ∫ x : Position, d x) +
      ((∫ x : Position, e x) - ∫ x : Position, f x) := by
  rw [integral_add
    (show Integrable (fun x => (a x - b x) + (c x - d x)) volume from (ha.sub hb).add (hc.sub hd))
    (show Integrable (fun x => e x - f x) volume from he.sub hf),
    integral_add (show Integrable (fun x => a x - b x) volume from ha.sub hb)
      (show Integrable (fun x => c x - d x) volume from hc.sub hd),
    integral_sub ha hb, integral_sub hc hd, integral_sub he hf]

theorem distributionCurl_eq_implies_hasWeakCurl (F G : Field)
    (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume)
    (hcurl : distributionCurl (fieldComponentDistribution F) = fieldComponentDistribution G) :
    HasWeakCurl F G := by
  intro φ hφ hs
  let ψ (i : Fin 3) : Position → ℂ := fun x => φ x i
  have hc (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    ((vectorCoordinate i).restrictScalars ℝ).contDiff.comp hφ
  have ht (i : Fin 3) : HasCompactSupport (ψ i) :=
    hs.comp_left (vectorCoordinate i).map_zero
  have hi (i j l : Fin 3) :
      Integrable (fun x : Position => (fderiv ℝ φ x (basisR j)) l * F x i) volume := by
    have hd : Continuous (fun x => (fderiv ℝ φ x (basisR j)) l) :=
      (vectorCoordinate l).continuous.comp
        ((hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const))
    have hs' : HasCompactSupport (fun x => (fderiv ℝ φ x (basisR j)) l) :=
      (hs.fderiv_apply ℝ (basisR j)).comp_left (vectorCoordinate l).map_zero
    exact compactTest_component_integrable F hF i _ hd hs'
  have hg (i : Fin 3) : Integrable (fun x : Position => φ x i * G x i) volume :=
    compactTest_component_integrable G hG i _ (hc i).continuous (ht i)
  have h0 := congrArg (fun T => complexTestEval (T 0) (ψ 0) (hc 0) (ht 0)) hcurl
  have h1 := congrArg (fun T => complexTestEval (T 1) (ψ 1) (hc 1) (ht 1)) hcurl
  have h2 := congrArg (fun T => complexTestEval (T 2) (ψ 2) (hc 2) (ht 2)) hcurl
  simp only [distributionCurl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, complexTestEval_sub, complexTestEval_partial_field F hF,
    complexTestEval_field G hG, ψ, testComponent_fderiv φ hφ] at h0 h1 h2
  have hleft : (∫ x : Position, bilinear (F x) (curl φ x)) =
      ((∫ x : Position, (fderiv ℝ φ x (basisR 1)) 2 * F x 0) -
        ∫ x : Position, (fderiv ℝ φ x (basisR 2)) 1 * F x 0) +
      ((∫ x : Position, (fderiv ℝ φ x (basisR 2)) 0 * F x 1) -
        ∫ x : Position, (fderiv ℝ φ x (basisR 0)) 2 * F x 1) +
      ((∫ x : Position, (fderiv ℝ φ x (basisR 0)) 1 * F x 2) -
        ∫ x : Position, (fderiv ℝ φ x (basisR 1)) 0 * F x 2) := by
    rw [← integral_three_sub _ _ _ _ _ _
      (hi 0 1 2) (hi 0 2 1) (hi 1 2 0) (hi 1 0 2) (hi 2 0 1) (hi 2 1 0)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp [bilinear, curl, Fin.sum_univ_three]
      ring
  have hright : (∫ x : Position, bilinear (G x) (φ x)) =
      (∫ x : Position, φ x 0 * G x 0) + (∫ x : Position, φ x 1 * G x 1) +
        ∫ x : Position, φ x 2 * G x 2 := by
    rw [← integral_add (hg 0) (hg 1),
      ← integral_add (show Integrable (fun x => φ x 0 * G x 0 + φ x 1 * G x 1) volume
        from (hg 0).add (hg 1)) (hg 2)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp [bilinear, Fin.sum_univ_three, mul_comm]
  rw [hleft, hright, ← h0, ← h1, ← h2]
  ring

theorem fieldComponentDistribution_add (F G : Field)
    (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume) (i : Fin 3) :
    fieldComponentDistribution (fun x => F x + G x) i =
      fieldComponentDistribution F i + fieldComponentDistribution G i := by
  ext φ
  have hiF : Integrable (fun x : Position => (φ x : ℂ) * F x i) volume := by
    exact (vectorCoordinate i).integrable_comp (φ.integrable_smul (hF.locallyIntegrableOn _))
  have hiG : Integrable (fun x : Position => (φ x : ℂ) * G x i) volume := by
    exact (vectorCoordinate i).integrable_comp (φ.integrable_smul (hG.locallyIntegrableOn _))
  rw [fieldComponentDistribution_apply (fun x => F x + G x) (hF.add hG), add_apply,
    fieldComponentDistribution_apply _ hF, fieldComponentDistribution_apply _ hG,
    ← integral_add hiF hiG]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [PiLp.add_apply, mul_add]

theorem fieldComponentDistribution_complex_smul (a : ℂ) (F : Field)
    (hF : LocallyIntegrable F volume) (i : Fin 3) :
    fieldComponentDistribution (fun x => a • F x) i = a • fieldComponentDistribution F i := by
  ext φ
  rw [fieldComponentDistribution_apply (fun x => a • F x) (hF.smul a)]
  change (∫ x : Position, (φ x : ℂ) * (a • F x) i) = a * fieldComponentDistribution F i φ
  rw [fieldComponentDistribution_apply _ hF, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [PiLp.smul_apply]; ring

theorem physicalSourceFields_first_weakCurl (k : ℝ) (p : CompactPolarization) :
    HasWeakCurl (electricVolumeField k p)
      (fun x => (Complex.I * (k : ℂ)) • magneticVolumeField k p x) := by
  have he := locallySquareIntegrable_locallyIntegrable _ (electricVolumeField_locallySquareIntegrable k p)
  have hm := locallySquareIntegrable_locallyIntegrable _ (magneticVolumeField_locallySquareIntegrable k p)
  refine distributionCurl_eq_implies_hasWeakCurl _ _ he
    (show LocallyIntegrable (fun x => (Complex.I * (k : ℂ)) • magneticVolumeField k p x) volume
      from hm.smul (Complex.I * (k : ℂ))) ?_
  rw [physicalSourceFields_first_curl]
  funext i
  exact (fieldComponentDistribution_complex_smul _ _ hm i).symm

theorem physicalSourceFields_second_weakCurl (k : ℝ) (p : CompactPolarization) :
    HasWeakCurl (magneticVolumeField k p)
      (fun x => (-Complex.I * (k : ℂ)) • (electricVolumeField k p x + p.current x)) := by
  have he := locallySquareIntegrable_locallyIntegrable _ (electricVolumeField_locallySquareIntegrable k p)
  have hm := locallySquareIntegrable_locallyIntegrable _ (magneticVolumeField_locallySquareIntegrable k p)
  have hp := (compactPolarization_current_integrable p).locallyIntegrable
  refine distributionCurl_eq_implies_hasWeakCurl _ _ hm
    (show LocallyIntegrable (fun x => (-Complex.I * (k : ℂ)) • (electricVolumeField k p x + p.current x)) volume
      from (he.add hp).smul (-Complex.I * (k : ℂ))) ?_
  rw [physicalSourceFields_second_curl]
  funext i
  rw [fieldComponentDistribution_complex_smul (-Complex.I * (k : ℂ))
      (fun x => electricVolumeField k p x + p.current x) (he.add hp),
    fieldComponentDistribution_add _ _ he hp]
  rfl

end OQ7Prescribed
