import work.SmoothDyadicRepresentation
import work.ScalarCompactConvolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
open scoped InnerProductSpace

theorem position_sum_basis (a : Position) : (∑ j : Fin 3, a j • basisR j) = a := by
  ext i
  fin_cases i <;> simp [basisR, Fin.sum_univ_succ]

theorem realCLM_basis_expansion (L : Position →L[ℝ] ℂ) (a : Position) :
    L a = ∑ j : Fin 3, (a j : ℂ) * L (basisR j) := by
  rw [← position_sum_basis a]
  simp only [map_sum, map_smul, Complex.real_smul]
  congr 1
  ext j
  rw [position_sum_basis]

def smoothPotentialDivergence (k : ℝ) (p : CompactPolarization) (x : Position) : ℂ :=
  ∑ j : Fin 3, smoothScalarPartial (smoothPotentialComponent k p j) j x

theorem smoothPotentialDivergence_contDiff (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPotentialDivergence k p) :=
  ContDiff.sum fun j _ => smoothScalarPartial_contDiff _
    (smoothPotentialComponent_contDiff k p hp j) j

theorem smoothDyadicComponent_eq_divergence_partial (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (i : Fin 3) (x : Position) :
    smoothDyadicComponent k p i x = (k ^ 2) • outgoingPotential k p x i +
      fderiv ℝ (smoothPotentialDivergence k p) x (basisR i) := by
  unfold smoothPotentialDivergence
  rw [fderiv_fun_sum (fun j _ =>
    (smoothScalarPartial_contDiff _ (smoothPotentialComponent_contDiff k p hp j) j).differentiable
      (by simp) x)]
  simp only [ContinuousLinearMap.sum_apply]
  rfl

theorem smoothDyadicField_axisCoupling (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (b : Position) (x : Position) :
    axisCoupling b (smoothDyadicField k p x) =
      (k ^ 2) • axisCoupling b (outgoingPotential k p x) +
        fderiv ℝ (smoothPotentialDivergence k p) x b := by
  unfold axisCoupling
  change (∑ i : Fin 3, (b i : ℂ) * smoothDyadicComponent k p i x) = _
  simp_rw [smoothDyadicComponent_eq_divergence_partial k p hp]
  rw [realCLM_basis_expansion (fderiv ℝ (smoothPotentialDivergence k p) x) b]
  simp only [mul_add, Finset.sum_add_distrib, mul_smul_comm, ← Finset.smul_sum]

theorem outgoingPotential_axis_source (k : ℝ) (p : CompactPolarization)
    (f : Position → ℂ) (a : Position) (hp : p.current = fun x => f x • complexify a)
    (x : Position) : outgoingPotential k p x = scalarOutgoingPotential k f x • complexify a := by
  change (∫ y : Position, outgoingGreen k (x - y) • p.current y) = _
  rw [hp]
  simp_rw [smul_smul]
  rw [integral_smul_const]
  rfl

theorem axisCoupling_complexify_inner (b a : Position) :
    axisCoupling b (complexify a) = (inner ℝ b a : ℂ) := by
  simp [axisCoupling, complexify, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem axisCoupling_smul_scalar (b : Position) (z : ℂ) (v : Vector) :
    axisCoupling b (z • v) = z * axisCoupling b v := by
  simp [axisCoupling, PiLp.smul_apply, Finset.mul_sum, mul_left_comm]

theorem smoothPotentialDivergence_axis_source (k : ℝ) (p : CompactPolarization)
    (f : Position → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (a : Position) (hp : p.current = fun x => f x • complexify a) :
    smoothPotentialDivergence k p = fun x => fderiv ℝ (scalarOutgoingPotential k f) x a := by
  have hP := scalarOutgoingPotential_contDiff k f hf hfc
  have he (j : Fin 3) : smoothPotentialComponent k p j =
      fun x => (a j : ℂ) • scalarOutgoingPotential k f x := by
    funext x
    rw [smoothPotentialComponent, outgoingPotential_axis_source k p f a hp]
    simp [complexify, PiLp.smul_apply, smul_eq_mul, mul_comm]
  funext x
  unfold smoothPotentialDivergence smoothScalarPartial
  simp_rw [he]
  simp_rw [fderiv_fun_const_smul (hP.differentiable (by simp) x), ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact (realCLM_basis_expansion (fderiv ℝ (scalarOutgoingPotential k f) x) a).symm

theorem smoothDyadicField_axis_source_projection (k : ℝ) (p : CompactPolarization)
    (f : Position → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (a b : Position) (hp : p.current = fun x => f x • complexify a) (x : Position) :
    axisCoupling b (smoothDyadicField k p x) =
      (k ^ 2 * inner ℝ b a : ℝ) • scalarOutgoingPotential k f x +
        fderiv ℝ (fun y => fderiv ℝ (scalarOutgoingPotential k f) y a) x b := by
  have hpc : ContDiff ℝ (⊤ : ℕ∞) p.current := by
    rw [hp]
    exact hf.smul contDiff_const
  rw [smoothDyadicField_axisCoupling k p hpc,
    smoothPotentialDivergence_axis_source k p f hf hfc a hp,
    outgoingPotential_axis_source k p f a hp, axisCoupling_smul_scalar,
    axisCoupling_complexify_inner]
  congr 1
  simp [Complex.real_smul, mul_assoc, mul_comm, mul_left_comm]

end OQ7Prescribed
