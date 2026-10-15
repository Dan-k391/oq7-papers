import PrescribedExtinction.RemovablePointIBP
import PrescribedExtinction.DynamicGreenRegularity
import PrescribedExtinction.NewtonContact

/-! The actual dynamic Green Hessian is its Newtonian distributional Hessian
plus its locally integrable classical difference. Both integrations by parts
use proved removable-point limits; no contact contribution is discarded. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Distributions

theorem dynamicScalarRemainder_test_ibp (k : ℝ) (j : Fin 3) (φ : ScalarTest) :
    (∫ x : Position, (testPartial j φ) x • dynamicScalarRemainder k x) =
      -(∫ x : Position, φ x • dynamicGradientRemainder k j x) := by
  apply removable_point_complex_test_ibp
    (dynamicScalarRemainder k) (dynamicGradientRemainder k j) j
    (dynamicScalarRemainder_contDiffAt k)
    (dynamicScalarRemainder_hasLineDerivAt k j)
    (dynamicScalarRemainder_locallyIntegrable k)
    (dynamicGradientRemainder_locallyIntegrable k j)
  exact ⟨1, by norm_num, dynamicScalarBound k 1,
    dynamicScalarBound_nonneg k 1 (by norm_num),
    fun x hx => dynamicScalarRemainder_norm_le_on_ball k 1 x hx⟩

theorem dynamicGradientRemainder_test_ibp (k : ℝ) (i j : Fin 3) (φ : ScalarTest) :
    (∫ x : Position, (testPartial i φ) x • dynamicGradientRemainder k j x) =
      -(∫ x : Position, φ x • dynamicHessianRemainder k i j x) := by
  apply removable_point_complex_test_ibp
    (dynamicGradientRemainder k j) (dynamicHessianRemainder k i j) i
    (dynamicGradientRemainder_contDiffAt k j)
    (dynamicGradientRemainder_hasLineDerivAt k i j)
    (dynamicGradientRemainder_locallyIntegrable k j)
    (dynamicHessianRemainder_locallyIntegrable k i j)
  exact ⟨1, by norm_num, dynamicGradientBound k 1,
    dynamicGradientBound_nonneg k 1 (by norm_num),
    fun x hx => dynamicGradientRemainder_norm_le_on_ball k 1 j x hx⟩

theorem dynamicScalarRemainder_double_ibp (k : ℝ) (i j : Fin 3) (φ : ScalarTest) :
    (∫ x : Position, (testPartial j (testPartial i φ)) x • dynamicScalarRemainder k x) =
      ∫ x : Position, φ x • dynamicHessianRemainder k i j x := by
  rw [dynamicScalarRemainder_test_ibp, dynamicGradientRemainder_test_ibp, neg_neg]

theorem greenHessian_eq_static_add_dynamic (k : ℝ) (i j : Fin 3) :
    greenHessian k i j = greenHessian 0 i j +
      Distribution.ofFun ⊤ (dynamicHessianRemainder k i j) volume ⊤ := by
  ext φ
  rw [add_apply, Distribution.ofFun_apply
    ((dynamicHessianRemainder_locallyIntegrable k i j).locallyIntegrableOn _),
    greenHessian_apply, greenHessian_apply,
    outgoingGreenDistribution_apply, outgoingGreenDistribution_apply,
    ← dynamicScalarRemainder_double_ibp k i j φ]
  have h0 := (testPartial j (testPartial i φ)).integrable_smul
    ((outgoingGreen_locallyIntegrable 0).locallyIntegrableOn _)
  have hk := (testPartial j (testPartial i φ)).integrable_smul
    ((outgoingGreen_locallyIntegrable k).locallyIntegrableOn _)
  simp only [dynamicScalarRemainder, smul_sub]
  rw [integral_sub hk h0]
  abel

theorem dyadicRemainderEntry_locallyIntegrable (k : ℝ) (i j : Fin 3) :
    LocallyIntegrable (fun x : Position => dyadicRemainder k x (basisC j) i) volume := by
  by_cases hij : i = j
  · have hg : LocallyIntegrable
        (fun x : Position => ((k ^ 2 : ℝ) : ℂ) * outgoingGreen k x) volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      exact ((outgoingGreen_locallyIntegrable k).integrableOn_isCompact hK).const_mul _
    have h := (dynamicHessianRemainder_locallyIntegrable k i j).add hg
    apply h.congr
    exact ae_of_all _ fun x => by simp [dynamicHessianRemainder, hij]
  · apply (dynamicHessianRemainder_locallyIntegrable k i j).congr
    exact ae_of_all _ fun x => by simp [dynamicHessianRemainder, hij]

theorem dyadicGreenDistribution_eq_static_add_remainder (k : ℝ) (i j : Fin 3) :
    dyadicGreenDistribution k i j = greenHessian 0 i j +
      Distribution.ofFun ⊤ (fun x : Position => dyadicRemainder k x (basisC j) i) volume ⊤ := by
  ext φ
  rw [add_apply, Distribution.ofFun_apply
    ((dyadicRemainderEntry_locallyIntegrable k i j).locallyIntegrableOn _)]
  rw [dyadicGreenDistribution, greenHessian_eq_static_add_dynamic]
  simp only [add_apply, Distribution.ofFun_apply
      ((dynamicHessianRemainder_locallyIntegrable k i j).locallyIntegrableOn _)]
  have hd := φ.integrable_smul
    ((dynamicHessianRemainder_locallyIntegrable k i j).locallyIntegrableOn _)
  have hg := φ.integrable_smul ((outgoingGreen_locallyIntegrable k).locallyIntegrableOn _)
  by_cases hij : i = j
  · subst i
    simp only [ite_true]
    rw [smul_apply, outgoingGreenDistribution_apply]
    have he : (fun x : Position => φ x • dyadicRemainder k x (basisC j) j) =
        (fun x => φ x • dynamicHessianRemainder k j j x +
          (k ^ 2) • (φ x • outgoingGreen k x)) := by
      funext x
      simp only [dynamicHessianRemainder, ite_true, smul_sub,
        Complex.real_smul]
      ring
    have hsg : Integrable (fun x : Position => (k ^ 2) • (φ x • outgoingGreen k x))
        volume := hg.smul (k ^ 2)
    rw [he, integral_add hd hsg, integral_smul]
    abel
  · simp only [hij, ite_false, zero_apply, zero_add]
    simp only [dynamicHessianRemainder, hij, ite_false, sub_zero]

theorem outgoing_dyadic_contact_identity (k : ℝ) (i j : Fin 3) :
    dyadicGreenDistribution k i j =
      newtonPVDistribution i j - ((if i = j then 1 else 0) / 3 : ℝ) • newtonDirac +
        Distribution.ofFun ⊤ (fun x : Position => dyadicRemainder k x (basisC j) i) volume ⊤ := by
  rw [dyadicGreenDistribution_eq_static_add_remainder,
    newton_hessian_contact_distribution]

end OQ7Prescribed
