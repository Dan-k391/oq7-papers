import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Tactic

/-! A vector integral-operator Schur estimate. The operator bound is derived
from an actual kernel pairing representation, scalar row/column integrals and
L² source norms. No desired operator norm is assumed in a structure field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]

theorem lp_integral_norm_sq (μ : Measure α) (f : Lp E 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  have h := Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f f)
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]
  rw [L2.inner_def] at hself
  rw [← hself]
  change (∫ x, ‖f x‖ ^ 2 ∂μ) = Complex.reCLM (∫ x, inner ℂ (f x) (f x) ∂μ)
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]

theorem weighted_row_integrable (μ : Measure α) [SFinite μ]
    (k : α × α → ℝ) (hk : AEStronglyMeasurable k (μ.prod μ))
    (hn : ∀ z, 0 ≤ k z) {C : ℝ} (_hC : 0 ≤ C)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (hbound : ∀ x, (∫ y, k (x, y) ∂μ) ≤ C)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ)
    (hg₂ : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun z : α × α => g z.1 ^ 2 * k z) (μ.prod μ) := by
  have hm : AEStronglyMeasurable (fun z : α × α => g z.1 ^ 2 * k z) (μ.prod μ) :=
    (hg.comp_fst.pow 2).mul hk
  have hi (x : α) : (∫ y, ‖g x ^ 2 * k (x, y)‖ ∂μ) =
      g x ^ 2 * (∫ y, k (x, y) ∂μ) := by
    calc
      _ = ∫ y, g x ^ 2 * k (x, y) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change ‖g x ^ 2 * k (x, y)‖ = g x ^ 2 * k (x, y)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hn _))]
      _ = _ := integral_const_mul _ _
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x => (hrow x).const_mul (g x ^ 2)
  · apply Integrable.mono' (hg₂.const_mul C) hm.norm.integral_prod_right'
    exact Filter.Eventually.of_forall fun x => by
      rw [hi]
      have hnint : 0 ≤ ∫ y, k (x, y) ∂μ := integral_nonneg fun y => hn _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hnint)]
      simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hbound x) (sq_nonneg (g x))

theorem weighted_row_integral_bound (μ : Measure α) [SFinite μ]
    (k : α × α → ℝ) (hk : AEStronglyMeasurable k (μ.prod μ))
    (hn : ∀ z, 0 ≤ k z) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (hbound : ∀ x, (∫ y, k (x, y) ∂μ) ≤ C)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ)
    (hg₂ : Integrable (fun x => g x ^ 2) μ) :
    (∫ z : α × α, g z.1 ^ 2 * k z ∂(μ.prod μ)) ≤ C * (∫ x, g x ^ 2 ∂μ) := by
  have hint := weighted_row_integrable μ k hk hn hC hrow hbound g hg hg₂
  rw [integral_prod _ hint]
  simp_rw [integral_const_mul]
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (integral_nonneg fun y => hn _)
  · exact hg₂.const_mul C
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hbound x) (sq_nonneg (g x))

/-- The norm of a bounded complex-linear operator follows from a quadratic
pairing bound by rescaling its two independent Hilbert-space inputs. -/
theorem operator_norm_of_quadratic_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ f g : H, ‖inner ℂ g (S f)‖ ≤ C / 2 * (‖g‖ ^ 2 + ‖f‖ ^ 2)) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound S hC
  intro f
  by_cases hf : f = 0
  · simp [hf]
  by_cases hSf : S f = 0
  · simp [hSf, mul_nonneg hC (norm_nonneg f)]
  let u : H := ((‖f‖⁻¹ : ℝ) : ℂ) • f
  let v : H := ((‖S f‖⁻¹ : ℝ) : ℂ) • S f
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hSpos : 0 < ‖S f‖ := norm_pos_iff.mpr hSf
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hfpos.ne']
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hSpos.ne']
  have hi : ‖inner ℂ v (S u)‖ = ‖S f‖ / ‖f‖ := by
    simp only [u, v, map_smul, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, Complex.conj_ofReal, norm_mul,
      Complex.norm_real, norm_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hfpos, abs_of_pos hSpos]
    field_simp <;> simp [RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have h := hpair u v
  rw [hi, hu, hv] at h
  norm_num at h
  exact (div_le_iff₀ hfpos).mp h

/-- The vector kernel pairing satisfies the Schur quadratic bound. All
integrability needed for the double integral is derived from the row/column
estimates and the L² inputs. -/
theorem kernel_pairing_schur (μ : Measure α) [SFinite μ]
    (K : α × α → E →L[ℂ] E) (hK : AEStronglyMeasurable K (μ.prod μ))
    (k : α × α → ℝ) (hk : AEStronglyMeasurable k (μ.prod μ))
    (hn : ∀ z, 0 ≤ k z) (hKn : ∀ z, ‖K z‖ ≤ k z)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (hrowC : ∀ x, (∫ y, k (x, y) ∂μ) ≤ C)
    (hcol : ∀ y, Integrable (fun x => k (x, y)) μ)
    (hcolC : ∀ y, (∫ x, k (x, y) ∂μ) ≤ C)
    (f g : Lp E 2 μ) :
    ‖∫ z : α × α, inner ℂ (g z.1) (K z (f z.2)) ∂(μ.prod μ)‖ ≤
      C / 2 * (‖g‖ ^ 2 + ‖f‖ ^ 2) := by
  have hgf : AEStronglyMeasurable (fun x => ‖g x‖) μ := (Lp.aestronglyMeasurable g).norm
  have hff : AEStronglyMeasurable (fun x => ‖f x‖) μ := (Lp.aestronglyMeasurable f).norm
  have hg₂ : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hf₂ : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hleft := weighted_row_integrable μ k hk hn hC hrow hrowC (fun x => ‖g x‖) hgf hg₂
  have hright' := weighted_row_integrable μ (fun z => k (z.2, z.1)) hk.prod_swap
    (fun z => hn (z.2, z.1)) hC hcol hcolC (fun x => ‖f x‖) hff hf₂
  have hright : Integrable (fun z : α × α => ‖f z.2‖ ^ 2 * k z) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using hright'.swap
  have hdom : Integrable (fun z : α × α =>
      (‖g z.1‖ ^ 2 * k z + ‖f z.2‖ ^ 2 * k z) / 2) (μ.prod μ) :=
    (hleft.add hright).div_const 2
  have hnphi (z : α × α) : ‖inner ℂ (g z.1) (K z (f z.2))‖ ≤
      (‖g z.1‖ ^ 2 * k z + ‖f z.2‖ ^ 2 * k z) / 2 := by
    have hop : ‖K z (f z.2)‖ ≤ k z * ‖f z.2‖ :=
      ((K z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hKn z) (norm_nonneg _))
    apply ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hop (norm_nonneg _))).trans
    have hs : 2 * ‖g z.1‖ * ‖f z.2‖ ≤ ‖g z.1‖ ^ 2 + ‖f z.2‖ ^ 2 :=
      two_mul_le_add_sq _ _
    have hm := mul_le_mul_of_nonneg_right hs (hn z)
    nlinarith
  have happ := (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).aestronglyMeasurable_comp₂
    hK (Lp.aestronglyMeasurable f).comp_snd
  have hphi : AEStronglyMeasurable
      (fun z : α × α => inner ℂ (g z.1) (K z (f z.2))) (μ.prod μ) :=
    (Lp.aestronglyMeasurable g).comp_fst.inner happ
  have hint : Integrable
      (fun z : α × α => inner ℂ (g z.1) (K z (f z.2))) (μ.prod μ) :=
    Integrable.mono' hdom hphi (Filter.Eventually.of_forall hnphi)
  have hbound := (norm_integral_le_integral_norm
    (fun z : α × α => inner ℂ (g z.1) (K z (f z.2)))).trans
    (integral_mono_ae hint.norm hdom (Filter.Eventually.of_forall hnphi))
  apply hbound.trans
  rw [integral_div, integral_add hleft hright]
  have hl := weighted_row_integral_bound μ k hk hn hC hrow hrowC (fun x => ‖g x‖) hgf hg₂
  have hr' := weighted_row_integral_bound μ (fun z => k (z.2, z.1)) hk.prod_swap
    (fun z => hn (z.2, z.1)) hC hcol hcolC (fun x => ‖f x‖) hff hf₂
  have hr : (∫ z : α × α, ‖f z.2‖ ^ 2 * k z ∂(μ.prod μ)) ≤ C * ‖f‖ ^ 2 := by
    rw [lp_integral_norm_sq μ f] at hr'
    rw [← integral_prod_swap]
    exact hr'
  rw [lp_integral_norm_sq μ g] at hl
  nlinarith

/-- The actual kernel representation, together with scalar Schur rows and
columns, proves the continuous-linear-map norm estimate. -/
theorem kernel_pairing_integrable (μ : Measure α) [SFinite μ]
    (K : α × α → E →L[ℂ] E) (hK : AEStronglyMeasurable K (μ.prod μ))
    (k : α × α → ℝ) (hk : AEStronglyMeasurable k (μ.prod μ))
    (hn : ∀ z, 0 ≤ k z) (hKn : ∀ z, ‖K z‖ ≤ k z)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (hrowC : ∀ x, (∫ y, k (x, y) ∂μ) ≤ C)
    (hcol : ∀ y, Integrable (fun x => k (x, y)) μ)
    (hcolC : ∀ y, (∫ x, k (x, y) ∂μ) ≤ C)
    (f g : Lp E 2 μ) :
    Integrable (fun z : α × α => inner ℂ (g z.1) (K z (f z.2))) (μ.prod μ) := by
  have hgf : AEStronglyMeasurable (fun x => ‖g x‖) μ := (Lp.aestronglyMeasurable g).norm
  have hff : AEStronglyMeasurable (fun x => ‖f x‖) μ := (Lp.aestronglyMeasurable f).norm
  have hg₂ : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hf₂ : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hleft := weighted_row_integrable μ k hk hn hC hrow hrowC (fun x => ‖g x‖) hgf hg₂
  have hright' := weighted_row_integrable μ (fun z => k (z.2, z.1)) hk.prod_swap
    (fun z => hn (z.2, z.1)) hC hcol hcolC (fun x => ‖f x‖) hff hf₂
  have hright : Integrable (fun z : α × α => ‖f z.2‖ ^ 2 * k z) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using hright'.swap
  have hdom : Integrable (fun z : α × α =>
      (‖g z.1‖ ^ 2 * k z + ‖f z.2‖ ^ 2 * k z) / 2) (μ.prod μ) :=
    (hleft.add hright).div_const 2
  have happ := (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).aestronglyMeasurable_comp₂
    hK (Lp.aestronglyMeasurable f).comp_snd
  apply Integrable.mono' hdom ((Lp.aestronglyMeasurable g).comp_fst.inner happ)
  exact Filter.Eventually.of_forall fun z => by
    have hop : ‖K z (f z.2)‖ ≤ k z * ‖f z.2‖ :=
      ((K z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hKn z) (norm_nonneg _))
    apply ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hop (norm_nonneg _))).trans
    have hm := mul_le_mul_of_nonneg_right (two_mul_le_add_sq ‖g z.1‖ ‖f z.2‖) (hn z)
    nlinarith

theorem integral_operator_schur (μ : Measure α) [SFinite μ]
    (S : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (K : α × α → E →L[ℂ] E) (hK : AEStronglyMeasurable K (μ.prod μ))
    (k : α × α → ℝ) (hk : AEStronglyMeasurable k (μ.prod μ))
    (hn : ∀ z, 0 ≤ k z) (hKn : ∀ z, ‖K z‖ ≤ k z)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (hrowC : ∀ x, (∫ y, k (x, y) ∂μ) ≤ C)
    (hcol : ∀ y, Integrable (fun x => k (x, y)) μ)
    (hcolC : ∀ y, (∫ x, k (x, y) ∂μ) ≤ C)
    (hrep : ∀ f g : Lp E 2 μ, inner ℂ g (S f) =
      ∫ z : α × α, inner ℂ (g z.1) (K z (f z.2)) ∂(μ.prod μ)) : ‖S‖ ≤ C := by
  apply operator_norm_of_quadratic_pairing S hC
  intro f g
  rw [hrep]
  exact kernel_pairing_schur μ K hK k hk hn hKn hC hrow hrowC hcol hcolC f g

end QuarticMaxwell
