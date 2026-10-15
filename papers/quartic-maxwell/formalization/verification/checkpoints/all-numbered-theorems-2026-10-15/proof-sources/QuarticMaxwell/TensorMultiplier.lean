import QuarticMaxwell.MaterialInverse
import PrescribedExtinction.SetSupportedL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual measurable susceptibility fields on an arbitrary measurable support.
The multiplier and its inverse are constructed from pointwise material bounds;
operator norm and coercivity are conclusions, not additional assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
namespace TensorMultiplier
open MeasureTheory Set
open OQ7Prescribed

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]

variable (μ : Measure α) (D : Set α) (A : α → E →L[ℂ] E)
  (hA : AEStronglyMeasurable A μ) (M : ℝ)
  (hcap : ∀ᵐ x ∂μ, x ∈ D → ‖A x‖ ≤ M)

include hcap in
theorem pointwise_bound (f : SetSupportedL2 (E := E) μ D) :
    ∀ᵐ x ∂μ, ‖A x ((f : Lp E 2 μ) x)‖ ≤ M * ‖(f : Lp E 2 μ) x‖ := by
  filter_upwards [hcap, f.property] with x hx hf
  by_cases hxd : x ∈ D
  · exact ((A x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hx hxd) (norm_nonneg _))
  · simp only [hf hxd, map_zero, norm_zero, mul_zero, le_refl]

include hA hcap in
theorem action_memLp (f : SetSupportedL2 (E := E) μ D) :
    MemLp (fun x => A x ((f : Lp E 2 μ) x)) 2 μ := by
  apply (Lp.memLp (f : Lp E 2 μ)).of_le_mul
    ((ContinuousLinearMap.apply ℂ E).aestronglyMeasurable_comp₂
      (Lp.aestronglyMeasurable (f : Lp E 2 μ)) hA)
  exact pointwise_bound μ D A M hcap f

def action (f : SetSupportedL2 (E := E) μ D) : SetSupportedL2 (E := E) μ D :=
  ⟨(action_memLp μ D A hA M hcap f).toLp (fun x => A x ((f : Lp E 2 μ) x)), by
    change ∀ᵐ x ∂μ, x ∉ D →
      ((action_memLp μ D A hA M hcap f).toLp (fun y => A y ((f : Lp E 2 μ) y))) x = 0
    filter_upwards [(action_memLp μ D A hA M hcap f).coeFn_toLp, f.property] with x hx hf
    intro hxd
    rw [hx, hf hxd, map_zero]⟩

theorem action_coe (f : SetSupportedL2 (E := E) μ D) :
    (action μ D A hA M hcap f : Lp E 2 μ) =ᵐ[μ]
      fun x => A x ((f : Lp E 2 μ) x) :=
  (action_memLp μ D A hA M hcap f).coeFn_toLp

theorem action_add (f g : SetSupportedL2 (E := E) μ D) :
    action μ D A hA M hcap (f + g) = action μ D A hA M hcap f + action μ D A hA M hcap g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [action_coe μ D A hA M hcap (f + g), action_coe μ D A hA M hcap f,
    action_coe μ D A hA M hcap g, Lp.coeFn_add (f : Lp E 2 μ) (g : Lp E 2 μ),
    Lp.coeFn_add (action μ D A hA M hcap f : Lp E 2 μ)
      (action μ D A hA M hcap g : Lp E 2 μ)] with x hfg hf hg hin hout
  rw [hfg]
  change A x (((f : Lp E 2 μ) + (g : Lp E 2 μ)) x) =
    ((action μ D A hA M hcap f : Lp E 2 μ) + (action μ D A hA M hcap g : Lp E 2 μ)) x
  rw [hout]
  rw [hin]
  simp only [Pi.add_apply]
  rw [hf, hg]
  exact map_add (A x) _ _

theorem action_smul (z : ℂ) (f : SetSupportedL2 (E := E) μ D) :
    action μ D A hA M hcap (z • f) = z • action μ D A hA M hcap f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [action_coe μ D A hA M hcap (z • f), action_coe μ D A hA M hcap f,
    Lp.coeFn_smul z (f : Lp E 2 μ),
    Lp.coeFn_smul z (action μ D A hA M hcap f : Lp E 2 μ)] with x hzf hf hin hout
  rw [hzf]
  change A x ((z • (f : Lp E 2 μ)) x) = (z • (action μ D A hA M hcap f : Lp E 2 μ)) x
  rw [hout]
  rw [hin]
  simp only [Pi.smul_apply]
  rw [hf]
  exact map_smul (A x) z _

def linear : SetSupportedL2 (E := E) μ D →ₗ[ℂ] SetSupportedL2 (E := E) μ D where
  toFun := action μ D A hA M hcap
  map_add' := action_add μ D A hA M hcap
  map_smul' := action_smul μ D A hA M hcap

theorem action_norm_le (f : SetSupportedL2 (E := E) μ D) :
    ‖action μ D A hA M hcap f‖ ≤ M * ‖f‖ := by
  change ‖(action μ D A hA M hcap f : Lp E 2 μ)‖ ≤ M * ‖(f : Lp E 2 μ)‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [action_coe μ D A hA M hcap f, pointwise_bound μ D A M hcap f] with x hx hb
  rw [hx]
  exact hb

def operator : SetSupportedL2 (E := E) μ D →L[ℂ] SetSupportedL2 (E := E) μ D :=
  (linear μ D A hA M hcap).mkContinuous M (action_norm_le μ D A hA M hcap)

theorem operator_coe (f : SetSupportedL2 (E := E) μ D) :
    (operator μ D A hA M hcap f : Lp E 2 μ) =ᵐ[μ]
      fun x => A x ((f : Lp E 2 μ) x) := action_coe μ D A hA M hcap f

theorem operator_norm_le (hM : 0 ≤ M) : ‖operator μ D A hA M hcap‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

theorem operator_coercive {m : ℝ}
    (hloss : ∀ᵐ x ∂μ, x ∈ D → ∀ v : E, m * ‖v‖ ^ 2 ≤ (inner ℂ v (A x v)).im)
    (f : SetSupportedL2 (E := E) μ D) :
    m * ‖f‖ ^ 2 ≤ (inner ℂ f (operator μ D A hA M hcap f)).im := by
  let J := operator μ D A hA M hcap
  have hi := L2.integrable_inner (𝕜 := ℂ) (f : Lp E 2 μ) (J f : Lp E 2 μ)
  have hii := L2.integrable_inner (𝕜 := ℂ) (f : Lp E 2 μ) (f : Lp E 2 μ)
  have hself (x : α) : (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re =
      ‖(f : Lp E 2 μ) x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hs : ∫ x, ‖(f : Lp E 2 μ) x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
    have hr := Complex.reCLM.integral_comp_comm hii
    change (∫ x, (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re ∂μ) =
      (inner ℂ (f : Lp E 2 μ) (f : Lp E 2 μ)).re at hr
    have he : (inner ℂ (f : Lp E 2 μ) (f : Lp E 2 μ)).re = ‖(f : Lp E 2 μ)‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    calc
      ∫ x, ‖(f : Lp E 2 μ) x‖ ^ 2 ∂μ =
          (inner ℂ (f : Lp E 2 μ) (f : Lp E 2 μ)).re := by simpa only [hself] using hr
      _ = ‖f‖ ^ 2 := he
  have hn : Integrable (fun x => ‖(f : Lp E 2 μ) x‖ ^ 2) μ := by
    have hn := hii.re
    change Integrable (fun x => (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re) μ at hn
    simpa only [hself] using hn
  have hm : m * ‖f‖ ^ 2 ≤ ∫ x, (inner ℂ ((f : Lp E 2 μ) x) ((J f : Lp E 2 μ) x)).im ∂μ := by
    rw [← hs, ← integral_const_mul]
    apply integral_mono_ae (hn.const_mul m) hi.im
    filter_upwards [operator_coe μ D A hA M hcap f, hloss, f.property] with x hx hl hf
    rw [hx]
    by_cases hxd : x ∈ D
    · exact hl hxd _
    · simp [hf hxd]
  have him := Complex.imCLM.integral_comp_comm hi
  change (∫ x, (inner ℂ ((f : Lp E 2 μ) x) ((J f : Lp E 2 μ) x)).im ∂μ) =
    (inner ℂ f (J f)).im at him
  exact hm.trans_eq him

variable [CompleteSpace E] (hD : MeasurableSet D) {m : ℝ} (hm : 0 < m)
  (hloss : ∀ᵐ x ∂μ, x ∈ D → ∀ v : E, m * ‖v‖ ^ 2 ≤ (inner ℂ v (A x v)).im)

def inverse : SetSupportedL2 (E := E) μ D →L[ℂ] SetSupportedL2 (E := E) μ D := by
  letI : IsClosed (setSupportedL2 (E := E) μ D : Set (Lp E 2 μ)) := setSupportedL2_isClosed μ D hD
  exact (materialInverseEquiv (operator μ D A hA M hcap) hm
    (operator_coercive μ D A hA M hcap hloss)).symm.toContinuousLinearMap

theorem operator_inverse (f : SetSupportedL2 (E := E) μ D) :
    operator μ D A hA M hcap (inverse μ D A hA M hcap hD hm hloss f) = f := by
  let : IsClosed (setSupportedL2 (E := E) μ D : Set (Lp E 2 μ)) := setSupportedL2_isClosed μ D hD
  exact (materialInverseEquiv (operator μ D A hA M hcap) hm
    (operator_coercive μ D A hA M hcap hloss)).apply_symm_apply f

theorem inverse_operator (f : SetSupportedL2 (E := E) μ D) :
    inverse μ D A hA M hcap hD hm hloss (operator μ D A hA M hcap f) = f := by
  let : IsClosed (setSupportedL2 (E := E) μ D : Set (Lp E 2 μ)) := setSupportedL2_isClosed μ D hD
  exact (materialInverseEquiv (operator μ D A hA M hcap) hm
    (operator_coercive μ D A hA M hcap hloss)).symm_apply_apply f

theorem inverse_norm_le : ‖inverse μ D A hA M hcap hD hm hloss‖ ≤ 1 / m := by
  let : IsClosed (setSupportedL2 (E := E) μ D : Set (Lp E 2 μ)) := setSupportedL2_isClosed μ D hD
  exact materialInverseEquiv_norm_le (operator μ D A hA M hcap) hm
    (operator_coercive μ D A hA M hcap hloss)

theorem inverse_loss_bound (hM : 0 < M) (f : SetSupportedL2 (E := E) μ D) :
    m / M ^ 2 * ‖f‖ ^ 2 ≤
      -(inner ℂ f (inverse μ D A hA M hcap hD hm hloss f)).im := by
  let : IsClosed (setSupportedL2 (E := E) μ D : Set (Lp E 2 μ)) := setSupportedL2_isClosed μ D hD
  exact inverse_loss_resource_bound (operator μ D A hA M hcap) hm hM
    (operator_norm_le μ D A hA M hcap hM.le) (operator_coercive μ D A hA M hcap hloss) f

/-- The constructed inverse solves the original pointwise constitutive law a.e. -/
theorem inverse_constitutive (f : SetSupportedL2 (E := E) μ D) :
    (fun x => A x ((inverse μ D A hA M hcap hD hm hloss f : Lp E 2 μ) x)) =ᵐ[μ]
      (f : Lp E 2 μ) := by
  have hc := operator_coe μ D A hA M hcap (inverse μ D A hA M hcap hD hm hloss f)
  rw [operator_inverse μ D A hA M hcap hD hm hloss] at hc
  exact hc.symm

end TensorMultiplier
end QuarticMaxwell
