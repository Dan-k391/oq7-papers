import PrescribedExtinction.Materials
import PrescribedExtinction.Maxwell
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Tactic.FunProp

/-! The explicit static Fourier multiplier `-ξ ξᵀ / |ξ|²` on vector L².
The multiplier and its norm bound are proved without any physical assumption.
Identifying it with the k=0 distributional Newton volume potential is a separate
unverified fundamental-solution/representation theorem. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

abbrev VectorL2 := Lp (α := Position) Vector 2 volume

def staticSymbol (ξ : Position) : Vector →L[ℂ] Vector :=
  -(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (complexify ξ) (complexify ξ)

theorem staticSymbol_apply (ξ : Position) (v : Vector) :
    staticSymbol ξ v = -(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • tensorApply (rankOne ξ) v := by
  rw [tensorApply_rankOne, axisCoupling_eq_inner]
  rfl

theorem staticSymbol_norm_le (ξ : Position) : ‖staticSymbol ξ‖ ≤ 1 := by
  have hnorm := complexify_norm_sq ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simp [staticSymbol, complexify]
  · have hp : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
    rw [staticSymbol, norm_smul, InnerProductSpace.norm_rankOne]
    rw [← sq, hnorm]
    simp [hp.ne']

theorem staticSymbol_apply_norm_le (ξ : Position) (v : Vector) :
    ‖staticSymbol ξ v‖ ≤ ‖v‖ := by
  calc
    ‖staticSymbol ξ v‖ ≤ ‖staticSymbol ξ‖ * ‖v‖ := (staticSymbol ξ).le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (staticSymbol_norm_le ξ) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem complexify_continuous : Continuous complexify := by
  unfold complexify
  fun_prop

theorem staticSymbol_memLp (f : VectorL2) :
    MemLp (fun ξ => staticSymbol ξ (f ξ)) 2 volume := by
  have hc : Measurable (fun ξ : Position => -(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by fun_prop
  have hu : AEStronglyMeasurable complexify volume :=
    complexify_continuous.measurable.aestronglyMeasurable
  have hi : AEStronglyMeasurable (fun ξ => inner ℂ (complexify ξ) (f ξ)) volume :=
    hu.inner (Lp.memLp f).aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun ξ => inner ℂ (complexify ξ) (f ξ) • complexify ξ) volume :=
    hi.smul hu
  have hm : AEStronglyMeasurable (fun ξ => staticSymbol ξ (f ξ)) volume := by
    change AEStronglyMeasurable
      (fun ξ => -(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • (inner ℂ (complexify ξ) (f ξ) • complexify ξ)) volume
    exact hc.aestronglyMeasurable.smul hv
  apply (Lp.memLp f).mono hm
  exact ae_of_all _ fun ξ => staticSymbol_apply_norm_le ξ (f ξ)

def staticMultiplierLp (f : VectorL2) : VectorL2 :=
  (staticSymbol_memLp f).toLp _

theorem staticMultiplierLp_coe (f : VectorL2) :
    staticMultiplierLp f =ᵐ[volume] fun ξ => staticSymbol ξ (f ξ) :=
  (staticSymbol_memLp f).coeFn_toLp

theorem staticMultiplierLp_norm_le (f : VectorL2) : ‖staticMultiplierLp f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [staticMultiplierLp_coe f] with ξ hξ
  rw [hξ]
  exact staticSymbol_apply_norm_le ξ (f ξ)

theorem staticMultiplierLp_add (f g : VectorL2) :
    staticMultiplierLp (f + g) = staticMultiplierLp f + staticMultiplierLp g := by
  apply Lp.ext
  filter_upwards [staticMultiplierLp_coe (f + g), staticMultiplierLp_coe f,
    staticMultiplierLp_coe g, Lp.coeFn_add f g,
    Lp.coeFn_add (staticMultiplierLp f) (staticMultiplierLp g)] with ξ hfg hf hg ha hb
  rw [hfg, ha, hb]
  change (staticSymbol ξ) (f ξ + g ξ) = staticMultiplierLp f ξ + staticMultiplierLp g ξ
  rw [map_add, hf, hg]

theorem staticMultiplierLp_smul (z : ℂ) (f : VectorL2) :
    staticMultiplierLp (z • f) = z • staticMultiplierLp f := by
  apply Lp.ext
  filter_upwards [staticMultiplierLp_coe (z • f), staticMultiplierLp_coe f,
    Lp.coeFn_smul z f, Lp.coeFn_smul z (staticMultiplierLp f)] with ξ hzf hf ha hb
  simp [hzf, ha, hb, hf]

def staticMultiplierLinear : VectorL2 →ₗ[ℂ] VectorL2 where
  toFun := staticMultiplierLp
  map_add' := staticMultiplierLp_add
  map_smul' := staticMultiplierLp_smul

def staticMultiplierCLM : VectorL2 →L[ℂ] VectorL2 :=
  staticMultiplierLinear.mkContinuous 1 fun f => by
    change ‖staticMultiplierLp f‖ ≤ 1 * ‖f‖
    simpa using staticMultiplierLp_norm_le f

theorem staticMultiplierCLM_norm_le : ‖staticMultiplierCLM‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- Fourier-conjugated explicit static multiplier. This is not yet a theorem
identifying the distributional volume operator with this bounded operator. -/
def staticFourierOperator : VectorL2 →L[ℂ] VectorL2 :=
  (Lp.fourierTransformₗᵢ Position Vector).symm.toLinearIsometry.toContinuousLinearMap ∘L
    staticMultiplierCLM ∘L
      (Lp.fourierTransformₗᵢ Position Vector).toLinearIsometry.toContinuousLinearMap

theorem staticFourierOperator_apply_norm_le (f : VectorL2) :
    ‖staticFourierOperator f‖ ≤ ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ Position Vector).symm
    (staticMultiplierLp ((Lp.fourierTransformₗᵢ Position Vector) f))‖ ≤ ‖f‖
  rw [(Lp.fourierTransformₗᵢ Position Vector).symm.norm_map]
  exact (staticMultiplierLp_norm_le _).trans_eq
    ((Lp.fourierTransformₗᵢ Position Vector).norm_map f)

theorem staticFourierOperator_norm_le : ‖staticFourierOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa using staticFourierOperator_apply_norm_le f

theorem staticSymbol_quadratic (ξ : Position) (v : Vector) :
    inner ℂ v (staticSymbol ξ v) =
      -(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (Complex.normSq (axisCoupling ξ v) : ℂ) := by
  have h : inner ℂ v (complexify ξ) = star (axisCoupling ξ v) := by
    rw [axisCoupling_eq_inner]
    exact (inner_conj_symm v (complexify ξ)).symm
  rw [staticSymbol, smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_smul_right, h, ← axisCoupling_eq_inner]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply]
  ring

theorem staticSymbol_quadratic_im (ξ : Position) (v : Vector) :
    (inner ℂ v (staticSymbol ξ v)).im = 0 := by
  rw [staticSymbol_quadratic]
  simp only [Complex.mul_im, Complex.neg_im, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, neg_zero]

theorem staticMultiplierLp_quadratic_im (f : VectorL2) :
    (inner ℂ f (staticMultiplierLp f)).im = 0 := by
  rw [L2.inner_def]
  have hi : (∫ ξ : Position, inner ℂ (f ξ) (staticMultiplierLp f ξ)).im =
      ∫ ξ : Position, (inner ℂ (f ξ) (staticMultiplierLp f ξ)).im :=
    (Complex.imCLM.integral_comp_comm
      (L2.integrable_inner (𝕜 := ℂ) f (staticMultiplierLp f))).symm
  rw [hi]
  apply integral_eq_zero_of_ae
  filter_upwards [staticMultiplierLp_coe f] with ξ hξ
  rw [hξ]
  exact staticSymbol_quadratic_im ξ (f ξ)

theorem staticFourierOperator_quadratic_im (f : VectorL2) :
    (inner ℂ f (staticFourierOperator f)).im = 0 := by
  rw [← (Lp.fourierTransformₗᵢ Position Vector).inner_map_map f (staticFourierOperator f)]
  change (inner ℂ ((Lp.fourierTransformₗᵢ Position Vector) f)
    ((Lp.fourierTransformₗᵢ Position Vector)
      ((Lp.fourierTransformₗᵢ Position Vector).symm
        (staticMultiplierLp ((Lp.fourierTransformₗᵢ Position Vector) f))))).im = 0
  rw [(Lp.fourierTransformₗᵢ Position Vector).apply_symm_apply]
  exact staticMultiplierLp_quadratic_im _

end OQ7Prescribed
