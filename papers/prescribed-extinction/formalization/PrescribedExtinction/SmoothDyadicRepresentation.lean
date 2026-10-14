import PrescribedExtinction.SmoothOutgoingFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

def smoothPotentialComponent (k : ℝ) (p : CompactPolarization) (j : Fin 3) : Position → ℂ :=
  fun x => outgoingPotential k p x j

def smoothScalarPartial (f : Position → ℂ) (j : Fin 3) : Position → ℂ :=
  fun x => fderiv ℝ f x (basisR j)

theorem smoothScalarPartial_contDiff (f : Position → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (smoothScalarPartial f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

def smoothDyadicComponent (k : ℝ) (p : CompactPolarization) (i : Fin 3) (x : Position) : ℂ :=
  (k ^ 2) • smoothPotentialComponent k p i x +
    ∑ j : Fin 3, smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i x

def smoothDyadicField (k : ℝ) (p : CompactPolarization) : Field :=
  fun x => WithLp.toLp 2 (fun i => smoothDyadicComponent k p i x)

theorem smoothPotentialComponent_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPotentialComponent k p j) :=
  (vectorCoordinate j).contDiff.comp (outgoingPotential_contDiff k p hp)

theorem smoothDyadicComponent_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDyadicComponent k p i) := by
  have hj (j : Fin 3) := smoothPotentialComponent_contDiff k p hp j
  exact ((hj i).const_smul (k ^ 2)).add (ContDiff.sum fun j _ =>
    smoothScalarPartial_contDiff _ (smoothScalarPartial_contDiff _ (hj j) j) i)

theorem smoothDyadicField_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) : ContDiff ℝ (⊤ : ℕ∞) (smoothDyadicField k p) := by
  exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr (smoothDyadicComponent_contDiff k p hp))

theorem smoothDyadicComponent_distribution (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (i : Fin 3) :
    Distribution.ofFun ⊤ (smoothDyadicComponent k p i) volume ⊤ = outgoingVolumeDistribution k p i := by
  have hj (j : Fin 3) := smoothPotentialComponent_contDiff k p hp j
  have hd (j : Fin 3) := smoothScalarPartial_contDiff _ (smoothScalarPartial_contDiff _ (hj j) j) i
  have he (j : Fin 3) : potentialComponentDistribution k p j =
      Distribution.ofFun ⊤ (smoothPotentialComponent k p j) volume ⊤ := by
    rw [potentialComponent_eq_fieldComponent]
    rfl
  rw [outgoingVolumeDistribution]
  have hpartials (j : Fin 3) :
      distributionPartial i (distributionPartial j (potentialComponentDistribution k p j)) =
      Distribution.ofFun ⊤ (smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i) volume ⊤ := by
    rw [he j, smoothScalar_distributionPartial _ (hj j)]
    change distributionPartial i (Distribution.ofFun ⊤
      (smoothScalarPartial (smoothPotentialComponent k p j) j) volume ⊤) = _
    exact smoothScalar_distributionPartial _ (smoothScalarPartial_contDiff _ (hj j) j) i
  simp_rw [hpartials, he]
  ext φ
  rw [Distribution.ofFun_apply ((smoothDyadicComponent_contDiff k p hp i).continuous.locallyIntegrable.locallyIntegrableOn ⊤)]
  simp only [add_apply, smul_apply, sum_apply]
  rw [Distribution.ofFun_apply ((hj i).continuous.locallyIntegrable.locallyIntegrableOn ⊤)]
  have happ (j : Fin 3) :
      (Distribution.ofFun ⊤ (smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i) volume ⊤) φ =
        ∫ x : Position, φ x • smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i x :=
    Distribution.ofFun_apply ((hd j).continuous.locallyIntegrable.locallyIntegrableOn ⊤)
  simp_rw [happ]
  change (∫ x : Position, φ x • ((k ^ 2) • smoothPotentialComponent k p i x +
      ∑ j : Fin 3, smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i x)) = _
  have hs (x : Position) : φ x • ((k ^ 2) • smoothPotentialComponent k p i x +
      ∑ j : Fin 3, smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i x) =
      (k ^ 2) • (φ x • smoothPotentialComponent k p i x) +
        ∑ j : Fin 3, φ x • smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i x := by
    rw [smul_add, Finset.smul_sum]
    congr 1
    rw [smul_smul, smul_smul, mul_comm]
  simp_rw [hs]
  have hzero : Integrable (fun x : Position => (k ^ 2) • (φ x • smoothPotentialComponent k p i x)) volume :=
    (φ.integrable_smul ((hj i).continuous.locallyIntegrable.locallyIntegrableOn ⊤)).smul (k ^ 2)
  have hsum : Integrable (fun x : Position => ∑ j : Fin 3,
      φ x • smoothScalarPartial (smoothScalarPartial (smoothPotentialComponent k p j) j) i x) volume :=
    integrable_finset_sum _ (fun j _ => φ.integrable_smul ((hd j).continuous.locallyIntegrable.locallyIntegrableOn ⊤))
  rw [integral_add hzero hsum, integral_smul,
    integral_finset_sum _ (fun j _ => φ.integrable_smul ((hd j).continuous.locallyIntegrable.locallyIntegrableOn ⊤))]

theorem smoothDyadicField_eq_electricVolumeField (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    smoothDyadicField k p =ᵐ[volume] electricVolumeField k p := by
  apply fieldComponentDistribution_injective _ _
    (smoothDyadicField_contDiff k p hp).continuous.locallyIntegrable
    (locallySquareIntegrable_locallyIntegrable _ (electricVolumeField_locallySquareIntegrable k p))
  funext i
  change Distribution.ofFun ⊤ (smoothDyadicComponent k p i) volume ⊤ = _
  rw [smoothDyadicComponent_distribution k p hp i, electricVolumeField_distribution]

end OQ7Prescribed
