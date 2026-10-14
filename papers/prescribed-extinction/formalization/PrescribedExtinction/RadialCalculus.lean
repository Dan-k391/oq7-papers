import PrescribedExtinction.GreenKernel
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Radial differentiation needed to justify the classical part of the Green
Hessian. These are actual derivatives, not definitions of candidate symbols.
No distributional contact identity follows from these punctured-space results. -/
noncomputable section
namespace OQ7Prescribed
open Filter
open scoped Topology

theorem radialNorm_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  convert h using 1
  · funext y
    simp [Real.sqrt_sq (norm_nonneg y)]
  · ext y
    simp only [Real.sqrt_sq (norm_nonneg x), smul_apply,
      smul_eq_mul]
    field_simp
    simp [two_smul]
    ring

theorem real_inner_basis (x : Position) (j : Fin 3) :
    inner ℝ x (basisR j) = x j := by
  simp [basisR, PiLp.inner_apply, RCLike.inner_apply]

theorem radial_lineDeriv (F : ℝ → ℂ) (F₁ : ℂ) (x : Position) (hx : x ≠ 0)
    (hF : HasDerivAt F F₁ ‖x‖) (j : Fin 3) :
    lineDeriv ℝ (fun y : Position => F ‖y‖) x (basisR j) =
      (x j / ‖x‖) • F₁ := by
  have h := hF.hasFDerivAt.comp x (radialNorm_hasFDerivAt x hx)
  have hd := (h.hasLineDerivAt (basisR j)).lineDeriv
  simpa [real_inner_basis, div_eq_mul_inv, mul_comm, mul_assoc, Function.comp_def] using hd

theorem radial_second_lineDeriv (F F₁ F₂ : ℝ → ℂ)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F (F₁ r) r)
    (hF₁ : ∀ r : ℝ, 0 < r → HasDerivAt F₁ (F₂ r) r)
    (x : Position) (hx : x ≠ 0) (i j : Fin 3) :
    lineDeriv ℝ (fun y : Position =>
      lineDeriv ℝ (fun z : Position => F ‖z‖) y (basisR j)) x (basisR i) =
      (x i * x j / ‖x‖ ^ 2) • F₂ ‖x‖ +
        ((if i = j then 1 else 0) / ‖x‖ - x i * x j / ‖x‖ ^ 3) • F₁ ‖x‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn := radialNorm_hasFDerivAt x hx
  have hi := (hasFDerivAt_inv hr.ne').comp x hn
  have hc := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Position →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hg := (hc.mul hi).smul ((hF₁ ‖x‖ hr).hasFDerivAt.comp x hn)
  have he : (fun y : Position => lineDeriv ℝ (fun z : Position => F ‖z‖) y (basisR j))
      =ᶠ[𝓝 x] (fun y : Position => (y j * ‖y‖⁻¹) • F₁ ‖y‖) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simpa [div_eq_mul_inv] using radial_lineDeriv F (F₁ ‖y‖) y hy
      (hF ‖y‖ (norm_pos_iff.mpr hy)) j
  have hd := ((hg.hasLineDerivAt (basisR i)).congr_of_eventuallyEq he).lineDeriv
  rw [hd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.proj_apply]
  split_ifs with hij <;>
    simp [hij, basisR, PiLp.inner_apply, RCLike.inner_apply,
      Complex.real_smul, div_eq_mul_inv] <;> ring

end OQ7Prescribed
