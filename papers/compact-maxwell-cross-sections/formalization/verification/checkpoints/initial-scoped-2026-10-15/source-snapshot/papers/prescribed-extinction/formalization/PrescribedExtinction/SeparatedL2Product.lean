import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped InnerProductSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem separatedProduct_memLp_two (f : α → ℂ) (g : β → ℂ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hi := ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).mul_prod
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg)
  simpa only [norm_mul, mul_pow] using hi

theorem memLp_two_integral_norm_sq (f : α → ℂ) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  have he := real_inner_self_eq_norm_sq (hf.toLp f)
  rw [L2.inner_def] at he
  simp_rw [real_inner_self_eq_norm_sq] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem separatedProduct_norm (f : α → ℂ) (g : β → ℂ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    ‖(separatedProduct_memLp_two f g hf hg).toLp (fun z : α × β => f z.1 * g z.2)‖ =
      ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hs := memLp_two_integral_norm_sq (fun z : α × β => f z.1 * g z.2)
    (separatedProduct_memLp_two f g hf hg)
  simp_rw [norm_mul, mul_pow] at hs
  rw [integral_prod_mul (fun x => ‖f x‖ ^ 2) (fun y => ‖g y‖ ^ 2), memLp_two_integral_norm_sq f hf,
    memLp_two_integral_norm_sq g hg] at hs
  have hn := norm_nonneg ((separatedProduct_memLp_two f g hf hg).toLp
    (fun z : α × β => f z.1 * g z.2))
  have hp := mul_nonneg (norm_nonneg (hf.toLp f)) (norm_nonneg (hg.toLp g))
  nlinarith

end OQ7Prescribed
