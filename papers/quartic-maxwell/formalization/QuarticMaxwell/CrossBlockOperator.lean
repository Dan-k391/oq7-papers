import QuarticMaxwell.StaticHessian
import QuarticMaxwell.RadiationTaylor

/-! The actual separated-source Newton-Hessian integral operator and its
rectangular L² norm. Static Fourier cross-block identification is separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace QuarticMaxwell.CrossBlockOperator
open MeasureTheory Set OQ7Prescribed StaticHessian

def field (D : Set Position) (f : VectorL2) (x : Position) : Vector :=
  ∫ y in D, newtonHessianOperator (x - y) (f y)

theorem kernel_norm_bound {D1 D2 : Set Position} {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)
    (x : Position) (hx : x ∈ D1) (y : Position) (hy : y ∈ D2) :
    ‖newtonHessianOperator (x - y)‖ ≤ 1 / (2 * Real.pi * d ^ 3) := by
  have hr := hgap x hx y hy
  have hn : x - y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hd hr)
  apply (newtonHessianOperator_norm_le (x - y) hn).trans
  gcongr

theorem integrand_aestronglyMeasurable (D : Set Position) (f : VectorL2) (x : Position) :
    AEStronglyMeasurable (fun y => newtonHessianOperator (x - y) (f y)) (volume.restrict D) := by
  have hK : Measurable (fun y => newtonHessianOperator (x - y)) :=
    newtonHessianOperator_measurable.comp (measurable_const.sub measurable_id)
  exact (ContinuousLinearMap.id ℂ (Vector →L[ℂ] Vector)).aestronglyMeasurable_comp₂
    hK.aestronglyMeasurable (Lp.aestronglyMeasurable f).restrict

theorem integrand_memLp {D1 D2 : Set Position} (hD2 : MeasurableSet D2) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)
    (f : VectorL2) (x : Position) (hx : x ∈ D1) :
    MemLp (fun y => newtonHessianOperator (x - y) (f y)) 2 (volume.restrict D2) := by
  let C := 1 / (2 * Real.pi * d ^ 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc := ((Lp.memLp f).restrict D2).const_smul (C : ℂ)
  apply hc.of_le (integrand_aestronglyMeasurable D2 f x)
  filter_upwards [ae_restrict_mem hD2] with y hy
  calc
    _ ≤ ‖newtonHessianOperator (x - y)‖ * ‖f y‖ := (newtonHessianOperator (x - y)).le_opNorm (f y)
    _ ≤ C * ‖f y‖ := mul_le_mul_of_nonneg_right (kernel_norm_bound hd hgap x hx y hy) (norm_nonneg _)
    _ = _ := by simp only [Pi.smul_apply]; rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

theorem integrand_integrable {D1 D2 : Set Position} (hD2 : MeasurableSet D2)
    (hfin2 : volume D2 ≠ ⊤) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)
    (f : VectorL2) (x : Position) (hx : x ∈ D1) :
    IntegrableOn (fun y => newtonHessianOperator (x - y) (f y)) D2 volume := by
  let : IsFiniteMeasure (volume.restrict D2) := ⟨by simpa using hfin2.lt_top⟩
  exact (integrand_memLp hD2 hd hgap f x hx).integrable (by norm_num)

theorem field_aestronglyMeasurable (D1 D2 : Set Position) (f : VectorL2) :
    AEStronglyMeasurable (field D2 f) (volume.restrict D1) := by
  have hK : Measurable (fun z : Position × Position => newtonHessianOperator (z.1 - z.2)) :=
    newtonHessianOperator_measurable.comp (measurable_fst.sub measurable_snd)
  have hm : AEStronglyMeasurable
      (fun z : Position × Position => newtonHessianOperator (z.1 - z.2) (f z.2))
      ((volume.restrict D1).prod (volume.restrict D2)) :=
    (ContinuousLinearMap.id ℂ (Vector →L[ℂ] Vector)).aestronglyMeasurable_comp₂
      hK.aestronglyMeasurable (Lp.aestronglyMeasurable f).restrict.comp_snd
  exact hm.integral_prod_right'

theorem field_pointwise_norm {D1 D2 : Set Position} (hD2 : MeasurableSet D2)
    (hfin2 : volume D2 ≠ ⊤) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)
    (f : VectorL2) (x : Position) (hx : x ∈ D1) :
    ‖field D2 f x‖ ≤ (1 / (2 * Real.pi * d ^ 3)) * (∫ y in D2, ‖f y‖) := by
  have hi : IntegrableOn (fun y => ‖f y‖) D2 volume :=
    (integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin2).norm
  unfold field
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.const_mul _)
  filter_upwards [ae_restrict_mem hD2] with y hy
  exact ((newtonHessianOperator (x - y)).le_opNorm (f y)).trans
    (mul_le_mul_of_nonneg_right (kernel_norm_bound hd hgap x hx y hy) (norm_nonneg _))

theorem field_memLp (D1 D2 : Set Position) (hD1 : MeasurableSet D1) (hD2 : MeasurableSet D2)
    (hfin1 : volume D1 ≠ ⊤) (hfin2 : volume D2 ≠ ⊤) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖) (f : VectorL2) :
    MemLp (field D2 f) 2 (volume.restrict D1) := by
  let : IsFiniteMeasure (volume.restrict D1) := ⟨by simpa using hfin1.lt_top⟩
  apply MemLp.of_bound (field_aestronglyMeasurable D1 D2 f)
    ((1 / (2 * Real.pi * d ^ 3)) * (∫ y in D2, ‖f y‖))
  filter_upwards [ae_restrict_mem hD1] with x hx
  exact field_pointwise_norm hD2 hfin2 hd hgap f x hx

theorem field_pointwise_square {D1 D2 : Set Position} (hD2 : MeasurableSet D2)
    (hfin2 : volume D2 ≠ ⊤) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)
    (f : VectorL2) (x : Position) (hx : x ∈ D1) :
    ‖field D2 f x‖ ^ 2 ≤ volume.real D2 * (1 / (2 * Real.pi * d ^ 3)) ^ 2 * ‖f‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict D2) := ⟨by simpa using hfin2.lt_top⟩
  let C := 1 / (2 * Real.pi * d ^ 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint := norm_integral_sq_le_measure_mul_square (volume.restrict D2)
    (fun y => newtonHessianOperator (x - y) (f y)) (integrand_memLp hD2 hd hgap f x hx)
  have hf₂ : Integrable (fun y => ‖f y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hb : (∫ y in D2, ‖newtonHessianOperator (x - y) (f y)‖ ^ 2) ≤ C ^ 2 * ‖f‖ ^ 2 := by
    calc
      _ ≤ ∫ y in D2, C ^ 2 * ‖f y‖ ^ 2 := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (hf₂.restrict.const_mul _)
        filter_upwards [ae_restrict_mem hD2] with y hy
        have hn := ((newtonHessianOperator (x - y)).le_opNorm (f y)).trans
          (mul_le_mul_of_nonneg_right (kernel_norm_bound hd hgap x hx y hy) (norm_nonneg _))
        nlinarith only [hn, norm_nonneg (newtonHessianOperator (x - y) (f y)),
          mul_nonneg hC (norm_nonneg (f y))]
      _ = C ^ 2 * (∫ y in D2, ‖f y‖ ^ 2) := integral_const_mul _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        rw [← lp_integral_norm_sq volume f]
        exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => sq_nonneg _) hf₂
  apply hpoint.trans
  simpa only [C, Measure.real, Measure.restrict_apply_univ, mul_assoc] using
    mul_le_mul_of_nonneg_left hb (show 0 ≤ volume.real D2 by positivity)

theorem field_add {D1 D2 : Set Position} (hD2 : MeasurableSet D2) (hfin2 : volume D2 ≠ ⊤)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)
    (f g : VectorL2) (x : Position) (hx : x ∈ D1) :
    field D2 (f + g) x = field D2 f x + field D2 g x := by
  unfold field
  rw [← integral_add (integrand_integrable hD2 hfin2 hd hgap f x hx)
    (integrand_integrable hD2 hfin2 hd hgap g x hx)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_add f g)] with y hy
  rw [hy]
  simp only [Pi.add_apply, map_add]

theorem field_smul (D2 : Set Position) (z : ℂ) (f : VectorL2) (x : Position) :
    field D2 (z • f) x = z • field D2 f x := by
  unfold field
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul z f)] with y hy
  rw [hy]
  simp only [Pi.smul_apply, map_smul]

section Operator
variable (D1 D2 : Set Position) (hD1 : MeasurableSet D1) (hD2 : MeasurableSet D2)
  (hfin1 : volume D1 ≠ ⊤) (hfin2 : volume D2 ≠ ⊤) (d : ℝ) (hd : 0 < d)
  (hgap : ∀ x ∈ D1, ∀ y ∈ D2, d ≤ ‖x - y‖)

def output (f : DomainL2 D2) : DomainL2 D1 := by
  let hf := (memLp_indicator_iff_restrict hD1).mpr
    (field_memLp D1 D2 hD1 hD2 hfin1 hfin2 hd hgap (f : VectorL2))
  refine ⟨hf.toLp (D1.indicator (field D2 (f : VectorL2))), ?_⟩
  filter_upwards [hf.coeFn_toLp] with x hx
  intro hxs
  rw [hx, indicator_of_notMem hxs]

theorem output_coe (f : DomainL2 D2) :
    (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2) =ᵐ[volume]
      D1.indicator (field D2 (f : VectorL2)) :=
  ((memLp_indicator_iff_restrict hD1).mpr
    (field_memLp D1 D2 hD1 hD2 hfin1 hfin2 hd hgap (f : VectorL2))).coeFn_toLp

theorem output_add (f g : DomainL2 D2) :
    output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap (f + g) =
      output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f + output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap (f + g),
    output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f,
    output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap g,
    Lp.coeFn_add (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2)
      (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap g : VectorL2)] with x hfg hf hg ha
  change (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap (f + g) : VectorL2) x =
    ((output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2) +
      (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap g : VectorL2)) x
  rw [hfg, ha]
  change _ = (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2) x +
    (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap g : VectorL2) x
  rw [hf, hg]
  by_cases hx : x ∈ D1
  · simp only [indicator_of_mem hx]
    exact field_add hD2 hfin2 hd hgap (f : VectorL2) (g : VectorL2) x hx
  · simp only [indicator_of_notMem hx, add_zero]

theorem output_smul (z : ℂ) (f : DomainL2 D2) :
    output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap (z • f) =
      z • output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap (z • f),
    output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f,
    Lp.coeFn_smul z (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2)] with x hzf hf hz
  change (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap (z • f) : VectorL2) x =
    (z • (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2)) x
  rw [hzf, hz]
  change _ = z • (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2) x
  rw [hf]
  by_cases hx : x ∈ D1
  · simp only [indicator_of_mem hx]
    exact field_smul D2 z (f : VectorL2) x
  · simp only [indicator_of_notMem hx, smul_zero]

theorem output_norm_sq (f : DomainL2 D2) :
    ‖output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f‖ ^ 2 ≤
      volume.real D1 * volume.real D2 * (1 / (2 * Real.pi * d ^ 3)) ^ 2 * ‖f‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict D1) := ⟨by simpa using hfin1.lt_top⟩
  calc
    _ = ∫ x in D1, ‖field D2 (f : VectorL2) x‖ ^ 2 := by
      change ‖(output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2)‖ ^ 2 = _
      rw [← lp_integral_norm_sq volume, ← integral_indicator hD1]
      apply integral_congr_ae
      filter_upwards [output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f] with x hx
      rw [hx]
      by_cases hxs : x ∈ D1 <;> simp [hxs]
    _ ≤ ∫ x in D1, volume.real D2 * (1 / (2 * Real.pi * d ^ 3)) ^ 2 * ‖f‖ ^ 2 := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _)
      filter_upwards [ae_restrict_mem hD1] with x hx
      exact field_pointwise_square hD2 hfin2 hd hgap (f : VectorL2) x hx
    _ = _ := by rw [integral_const]; simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]; ring

theorem output_norm (f : DomainL2 D2) :
    ‖output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f‖ ≤
      (Real.sqrt (volume.real D1 * volume.real D2) / (2 * Real.pi * d ^ 3)) * ‖f‖ := by
  have hh := output_norm_sq D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f
  have hh' : ‖output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f‖ ^ 2 ≤
      (1 / (2 * Real.pi * d ^ 3)) ^ 2 * (volume.real D1 * volume.real D2) * ‖f‖ ^ 2 := by
    convert hh using 1; ring
  have hn := nonnegative_norm_of_square_bound (norm_nonneg _) (norm_nonneg _)
    (by positivity : 0 ≤ 1 / (2 * Real.pi * d ^ 3)) (by positivity : 0 ≤ volume.real D1 * volume.real D2) hh'
  convert hn using 1; ring

def linear : DomainL2 D2 →ₗ[ℂ] DomainL2 D1 where
  toFun := output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap
  map_add' := output_add D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap
  map_smul' := output_smul D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap

def operator : DomainL2 D2 →L[ℂ] DomainL2 D1 :=
  (linear D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap).mkContinuous
    (Real.sqrt (volume.real D1 * volume.real D2) / (2 * Real.pi * d ^ 3))
    (output_norm D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap)

theorem operator_norm_le : ‖operator D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap‖ ≤
    Real.sqrt (volume.real D1 * volume.real D2) / (2 * Real.pi * d ^ 3) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

include hD2 in
theorem field_eq_full_integral (f : DomainL2 D2) (x : Position) :
    field D2 (f : VectorL2) x = ∫ y, newtonHessianOperator (x - y) ((f : VectorL2) y) := by
  unfold field
  rw [← integral_indicator hD2]
  apply integral_congr_ae
  filter_upwards [f.property] with y hy
  by_cases hys : y ∈ D2
  · simp only [indicator_of_mem hys]
  · rw [indicator_of_notMem hys, hy hys, map_zero]

theorem operator_coe_on (f : DomainL2 D2) :
    ∀ᵐ x ∂volume, x ∈ D1 →
      (operator D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2) x =
        ∫ y, newtonHessianOperator (x - y) ((f : VectorL2) y) := by
  filter_upwards [output_coe D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f] with x hx
  intro hxs
  change (output D1 D2 hD1 hD2 hfin1 hfin2 d hd hgap f : VectorL2) x = _
  rw [hx, indicator_of_mem hxs, field_eq_full_integral D2 hD2 f x]

end Operator

end QuarticMaxwell.CrossBlockOperator
