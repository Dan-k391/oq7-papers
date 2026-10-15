import PrescribedExtinction.ExteriorKernelTests
import Mathlib.MeasureTheory.Group.Prod

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem exterior_current_test_joint_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0)
    (i j : Fin 3) :
    Integrable (fun q : Position × Position => (φ q.1 : ℂ) *
      classicalDyadic k (q.1 - q.2) (basisC j) i * p.current q.2 j) (volume.prod volume) := by
  have hker : Measurable (fun q : Position × Position =>
      classicalDyadic k (q.1 - q.2) (basisC j) i) := by
    exact (vectorCoordinate i).measurable.comp
      ((ContinuousLinearMap.apply ℂ Vector (basisC j)).measurable.comp
        ((classicalDyadic_measurable k).comp (measurable_fst.sub measurable_snd)))
  have ht : AEStronglyMeasurable (fun q : Position × Position => (φ q.1 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  have hm := (ht.mul hker.aestronglyMeasurable).mul
    (current_component_integrable p j).aestronglyMeasurable.comp_snd
  have hen := ((φ.continuous.integrable_of_hasCompactSupport (μ := volume) φ.hasCompactSupport).norm.mul_prod
    (current_component_integrable p j).norm).const_mul (exteriorKernelBound k)
  apply hen.mono' hm
  apply ae_of_all
  intro q
  change ‖(φ q.1 : ℂ) * classicalDyadic k (q.1 - q.2) (basisC j) i * p.current q.2 j‖ ≤
    exteriorKernelBound k * (‖φ q.1‖ * ‖p.current q.2 j‖)
  by_cases hx : ‖q.1‖ ≤ p.radius + 1
  · simp [hφ q.1 hx]
  by_cases hy : ‖q.2‖ ≤ p.radius
  · have hd : 1 ≤ ‖q.1 - q.2‖ := by linarith [norm_sub_norm_le q.1 q.2]
    have hb := (PiLp.norm_apply_le (classicalDyadic k (q.1 - q.2) (basisC j)) i).trans
      (classicalDyadic_norm_le_far k (q.1 - q.2) hd (basisC j))
    have hn : ‖basisC j‖ = 1 := by simp [basisC]
    rw [hn, mul_one] at hb
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |φ q.1| * exteriorKernelBound k * ‖p.current q.2 j‖ := by gcongr
      _ = _ := by ring
  · simp [p.vanish q.2 (lt_of_not_ge hy)]

theorem exterior_current_correlation_joint_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0)
    (i j : Fin 3) :
    Integrable (fun q : Position × Position => (φ (q.1 + q.2) : ℂ) *
      classicalDyadic k q.1 (basisC j) i * p.current q.2 j) (volume.prod volume) := by
  have h := (measurePreserving_add_prod (volume : Measure Position) (volume : Measure Position)).integrable_comp_of_integrable
    (exterior_current_test_joint_integrable k p φ hφ i j)
  simpa only [Function.comp_def, add_sub_cancel_right] using h

theorem exterior_current_component_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0)
    (i j : Fin 3) :
    (∫ x : Position, ∫ y : Position, (φ x : ℂ) *
      classicalDyadic k (x - y) (basisC j) i * p.current y j) =
    ∫ z : Position, newtonCurrentCorrelation p φ j z * classicalDyadic k z (basisC j) i := by
  calc
    _ = ∫ y : Position, ∫ x : Position, (φ x : ℂ) *
      classicalDyadic k (x - y) (basisC j) i * p.current y j :=
      integral_integral_swap (exterior_current_test_joint_integrable k p φ hφ i j)
    _ = ∫ y : Position, ∫ z : Position, (φ (z + y) : ℂ) *
      classicalDyadic k z (basisC j) i * p.current y j := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        have h := integral_add_right_eq_self (μ := (volume : Measure Position))
          (fun x : Position => (φ x : ℂ) * classicalDyadic k (x - y) (basisC j) i * p.current y j) y
        simpa only [add_sub_cancel_right] using h.symm
    _ = ∫ z : Position, ∫ y : Position, (φ (z + y) : ℂ) *
      classicalDyadic k z (basisC j) i * p.current y j :=
      (integral_integral_swap (exterior_current_correlation_joint_integrable k p φ hφ i j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change (∫ y : Position, (φ (z + y) : ℂ) * classicalDyadic k z (basisC j) i * p.current y j) =
          newtonCurrentCorrelation p φ j z * classicalDyadic k z (basisC j) i
        unfold newtonCurrentCorrelation
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by ring

theorem exteriorElectric_test_pointwise (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0)
    (i : Fin 3) (x : Position) :
    (∑ j : Fin 3, ∫ y : Position, (φ x : ℂ) *
      classicalDyadic k (x - y) (basisC j) i * p.current y j) =
      (φ x : ℂ) * exteriorElectric k p x i := by
  by_cases hx : ‖x‖ ≤ p.radius + 1
  · simp [hφ x hx]
  · have hi := exteriorElectric_integrable_far k p x (le_of_lt (lt_of_not_ge hx))
    have hb (j : Fin 3) : Integrable (fun y : Position =>
        (φ x : ℂ) * classicalDyadic k (x - y) (basisC j) i * p.current y j) volume := by
      have hm := (current_component_integrable p j).aestronglyMeasurable
      have hmker : Measurable (fun y : Position => classicalDyadic k (x - y) (basisC j) i) := by
        exact (vectorCoordinate i).measurable.comp
          ((ContinuousLinearMap.apply ℂ Vector (basisC j)).measurable.comp
            ((classicalDyadic_measurable k).comp (measurable_const.sub measurable_id)))
      apply ((current_component_integrable p j).norm.const_mul
        (‖(φ x : ℂ)‖ * exteriorKernelBound k)).mono' ((hmker.aestronglyMeasurable.const_mul _).mul hm)
      apply ae_of_all
      intro y
      change ‖(φ x : ℂ) * classicalDyadic k (x - y) (basisC j) i * p.current y j‖ ≤ _
      by_cases hy : ‖y‖ ≤ p.radius
      · have hd : 1 ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
        have hb := (PiLp.norm_apply_le (classicalDyadic k (x - y) (basisC j)) i).trans
          (classicalDyadic_norm_le_far k (x - y) hd (basisC j))
        simp only [show ‖basisC j‖ = 1 by simp [basisC], mul_one] at hb
        simp only [norm_mul]
        gcongr
      · simp [p.vanish y (lt_of_not_ge hy)]
    change (∑ j : Fin 3, ∫ y : Position, (φ x : ℂ) *
      classicalDyadic k (x - y) (basisC j) i * p.current y j) = _
    rw [← integral_finsetSum _ fun j _ => hb j]
    unfold exteriorElectric
    change _ = (φ x : ℂ) * (vectorCoordinate i)
      (∫ y : Position, classicalDyadic k (x - y) (p.current y))
    rw [← (vectorCoordinate i).integral_comp_comm hi, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change (∑ j : Fin 3, (φ x : ℂ) * classicalDyadic k (x - y) (basisC j) i * p.current y j) =
        (φ x : ℂ) * classicalDyadic k (x - y) (p.current y) i
      rw [vector_clm_coordinate_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem exteriorElectric_test_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0) (i : Fin 3) :
    Integrable (fun x : Position => (φ x : ℂ) * exteriorElectric k p x i) volume := by
  have hj (j : Fin 3) := (exterior_current_test_joint_integrable k p φ hφ i j).integral_prod_left
  apply (integrable_finsetSum Finset.univ fun j _ => hj j).congr
  exact ae_of_all _ fun x => exteriorElectric_test_pointwise k p φ hφ i x

theorem exteriorElectric_test_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0) (i : Fin 3) :
    (∫ x : Position, (φ x : ℂ) * exteriorElectric k p x i) =
      outgoingVolumeDistribution k p i φ := by
  have hj (j : Fin 3) := (exterior_current_test_joint_integrable k p φ hφ i j).integral_prod_left
  have hid : (fun x : Position => (φ x : ℂ) * exteriorElectric k p x i) =ᵐ[volume]
      (fun x => ∑ j : Fin 3, ∫ y : Position, (φ x : ℂ) *
        classicalDyadic k (x - y) (basisC j) i * p.current y j) := by
    apply ae_of_all
    intro x
    exact (exteriorElectric_test_pointwise k p φ hφ i x).symm
  rw [integral_congr_ae hid, integral_finsetSum _ fun j _ => hj j]
  simp_rw [exterior_current_component_pairing k p φ hφ i]
  rw [outgoingVolumeDistribution_current_dyadic_pairing]
  apply Finset.sum_congr rfl
  intro j _
  exact (currentDyadicTestPairing_exterior_integral k p φ (fun x hx => hφ x (by linarith)) i j).symm

def currentExterior (p : CompactPolarization) : TopologicalSpace.Opens Position :=
  ⟨{x : Position | p.radius + 1 < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩

theorem exteriorElectric_aestronglyMeasurable (k : ℝ) (p : CompactPolarization) :
    AEStronglyMeasurable (exteriorElectric k p) volume :=
  p.memLp.aestronglyMeasurable.convolution (L := vectorOperatorApply)
    (classicalDyadic_measurable k).aestronglyMeasurable

theorem exteriorElectric_norm_le (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : p.radius + 1 ≤ ‖x‖) :
    ‖exteriorElectric k p x‖ ≤ exteriorKernelBound k * ∫ y : Position, ‖p.current y‖ := by
  unfold exteriorElectric
  calc
    _ ≤ ∫ y : Position, exteriorKernelBound k * ‖p.current y‖ := by
      apply norm_integral_le_of_norm_le ((compactPolarization_current_integrable p).norm.const_mul _)
      apply ae_of_all
      intro y
      by_cases hy : ‖y‖ ≤ p.radius
      · exact classicalDyadic_norm_le_far k (x - y) (by linarith [norm_sub_norm_le x y]) _
      · simp [p.vanish y (lt_of_not_ge hy)]
    _ = _ := integral_const_mul _ _

theorem exteriorElectric_locallyIntegrableOn (k : ℝ) (p : CompactPolarization) :
    LocallyIntegrableOn (exteriorElectric k p) (currentExterior p) volume := by
  rw [locallyIntegrableOn_iff (currentExterior p).isOpen.isLocallyClosed]
  intro K hK hcompact
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hcompact.measure_lt_top⟩
  apply Integrable.of_bound ((exteriorElectric_aestronglyMeasurable k p).restrict)
    (exteriorKernelBound k * ∫ y : Position, ‖p.current y‖)
  apply ae_restrict_of_forall_mem hcompact.measurableSet
  intro x hx
  exact exteriorElectric_norm_le k p x (hK hx).le

theorem exteriorElectric_component_locallyIntegrableOn (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) :
    LocallyIntegrableOn (fun x => exteriorElectric k p x i) (currentExterior p) volume :=
  (vectorCoordinate i).locallyIntegrableOn_comp (exteriorElectric_locallyIntegrableOn k p)

theorem electricVolumeField_component_locallyIntegrableOn (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) :
    LocallyIntegrableOn (fun x => electricVolumeField k p x i) (currentExterior p) volume :=
  (vectorCoordinate i).locallyIntegrableOn_comp
    ((locallySquareIntegrable_locallyIntegrable _
      (electricVolumeField_locallySquareIntegrable k p)).locallyIntegrableOn _)

theorem electricExterior_component_distribution (k : ℝ) (p : CompactPolarization) (i : Fin 3) :
    Distribution.ofFun (currentExterior p) (fun x => exteriorElectric k p x i) volume ⊤ =
      Distribution.ofFun (currentExterior p) (fun x => electricVolumeField k p x i) volume ⊤ := by
  ext ψ
  let φ : ScalarTest := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, Set.subset_univ _⟩
  have hφ : ∀ x : Position, ‖x‖ ≤ p.radius + 1 → φ x = 0 := by
    intro x hx
    exact ψ.zero_on_compl (show x ∈ (currentExterior p : Set Position)ᶜ from not_lt.mpr hx)
  rw [Distribution.ofFun_apply (exteriorElectric_component_locallyIntegrableOn k p i),
    Distribution.ofFun_apply (electricVolumeField_component_locallyIntegrableOn k p i)]
  simp only [Complex.real_smul]
  change (∫ x : Position, (φ x : ℂ) * exteriorElectric k p x i) =
    ∫ x : Position, (φ x : ℂ) * electricVolumeField k p x i
  rw [exteriorElectric_test_pairing k p φ hφ i,
    ← fieldComponentDistribution_apply _ (locallySquareIntegrable_locallyIntegrable _
      (electricVolumeField_locallySquareIntegrable k p)), electricVolumeField_distribution]

theorem electricExterior_eq_ae (k : ℝ) (p : CompactPolarization) :
    exteriorElectric k p =ᵐ[volume.restrict (currentExterior p)] electricVolumeField k p := by
  have h (i : Fin 3) := Distribution.ofFun_injective
    (exteriorElectric_component_locallyIntegrableOn k p i)
    (electricVolumeField_component_locallyIntegrableOn k p i)
    (electricExterior_component_distribution k p i)
  filter_upwards [h 0, h 1, h 2] with x h0 h1 h2
  ext i
  fin_cases i <;> assumption

end OQ7Prescribed
