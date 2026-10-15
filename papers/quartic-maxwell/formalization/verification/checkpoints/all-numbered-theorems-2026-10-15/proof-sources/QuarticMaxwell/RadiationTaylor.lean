import QuarticMaxwell.RadiationGram
import QuarticMaxwell.SourceTaylor

/-! Derived bounded-amplitude radiation estimates, used for the actual
exponential phase Taylor remainder and the even Gram-operator expansion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem boundedRadiation_integrand_memLp (D : Set Position) (hD : MeasurableSet D)
    (a : UnitSphere → Position → ℂ) (ha : ∀ n, Measurable (a n)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ n y, y ∈ D → ‖a n y‖ ≤ c) (f : VectorL2) (n : UnitSphere) :
    MemLp (fun y => a n y • angularProjection n (f y)) 2 (volume.restrict D) := by
  apply ((Lp.memLp f).restrict D).of_le_mul
    (((ha n).aestronglyMeasurable.smul
      ((angularProjection n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))).restrict)
  filter_upwards [ae_restrict_mem hD] with y hy
  change ‖a n y • angularProjection n (f y)‖ ≤ c * ‖f y‖
  rw [norm_smul]
  exact mul_le_mul (hbound n y hy) (angularProjection_apply_norm_le n (f y)) (norm_nonneg _) hc

theorem boundedRadiation_field_square_bound (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (a : UnitSphere → Position → ℂ) (ha : ∀ n, Measurable (a n))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ n y, y ∈ D → ‖a n y‖ ≤ c) (f : VectorL2) :
    (∫ n : UnitSphere, ‖∫ y in D, a n y • angularProjection n (f y)‖ ^ 2 ∂sphereArea) ≤
      c ^ 2 * (8 * Real.pi * volume.real D / 3) * ‖f‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin.lt_top⟩
  have hpoint (n : UnitSphere) :
      ‖∫ y in D, a n y • angularProjection n (f y)‖ ^ 2 ≤
        (volume.real D * c ^ 2) * (∫ y in D, ‖angularProjection n (f y)‖ ^ 2) := by
    have hcs := norm_integral_sq_le_measure_mul_square (volume.restrict D)
      (fun y => a n y • angularProjection n (f y))
      (boundedRadiation_integrand_memLp D hD a ha hc hbound f n)
    have hmem : MemLp (fun y => angularProjection n (f y)) 2 (volume.restrict D) :=
      ((Lp.memLp f).restrict D).of_le
        ((angularProjection n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).restrict
        (ae_of_all _ fun y => angularProjection_apply_norm_le n (f y))
    have hi : Integrable (fun y => c ^ 2 * ‖angularProjection n (f y)‖ ^ 2) (volume.restrict D) :=
      ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem).const_mul _
    have hinner : (∫ y in D, ‖a n y • angularProjection n (f y)‖ ^ 2) ≤
        c ^ 2 * (∫ y in D, ‖angularProjection n (f y)‖ ^ 2) := by
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg (ae_of_all _ fun y => sq_nonneg _) hi
      filter_upwards [ae_restrict_mem hD] with y hy
      rw [norm_smul, mul_pow]
      have h := hbound n y hy
      have hs : ‖a n y‖ ^ 2 ≤ c ^ 2 := by nlinarith [norm_nonneg (a n y)]
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    have h := hcs.trans (mul_le_mul_of_nonneg_left hinner (measureReal_nonneg))
    simpa [Measure.real, mul_assoc] using h
  have hj := projection_square_joint_integrable D f
  have houter : (∫ n : UnitSphere, ‖∫ y in D, a n y • angularProjection n (f y)‖ ^ 2 ∂sphereArea) ≤
      (volume.real D * c ^ 2) * (∫ n : UnitSphere, (∫ y in D,
        ‖angularProjection n (f y)‖ ^ 2) ∂sphereArea) := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun n => sq_nonneg _)
      (hj.integral_prod_left.const_mul _) (ae_of_all _ hpoint)
  have hswap : (∫ n : UnitSphere, (∫ y in D, ‖angularProjection n (f y)‖ ^ 2) ∂sphereArea) =
      8 * Real.pi / 3 * (∫ y in D, ‖f y‖ ^ 2) := by
    rw [integral_integral_swap hj]
    simp only [angularProjection_integral, integral_const_mul]
  rw [hswap] at houter
  have hf₂ : Integrable (fun y : Position => ‖f y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hsource : (∫ y in D, ‖f y‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    rw [← lp_integral_norm_sq volume f]
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun y => sq_nonneg _) hf₂
  have hscaled := mul_le_mul_of_nonneg_left hsource
    (show 0 ≤ (volume.real D * c ^ 2) * (8 * Real.pi / 3) by positivity)
  apply houter.trans
  nlinarith only [hscaled]

theorem operator_norm_sq_of_apply_sq {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (A : H →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f, ‖A f‖ ^ 2 ≤ C * ‖f‖ ^ 2) : ‖A‖ ^ 2 ≤ C := by
  have hs := Real.sq_sqrt hC
  have hn : ‖A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    have hf := h f
    have heq : (Real.sqrt C * ‖f‖) ^ 2 = C * ‖f‖ ^ 2 := by rw [mul_pow, hs]
    nlinarith only [hf, heq, norm_nonneg (A f), mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f)]
  nlinarith only [hn, hs, norm_nonneg A, Real.sqrt_nonneg C]

theorem radiationPhase_sub_one_norm_bound (k : ℝ) (n : UnitSphere) (y : Position) :
    ‖radiationPhase k n y - 1‖ ≤ |k| * ‖y‖ := by
  have hp := purePhase_difference_le (-k * inner ℝ (n : Position) y) 0
  have he : -Complex.I * ((k * inner ℝ (n : Position) y : ℝ) : ℂ) =
      Complex.I * ((-k * inner ℝ (n : Position) y : ℝ) : ℂ) := by push_cast; ring
  have hi := abs_real_inner_le_norm (n : Position) y
  rw [unitSphere_norm, one_mul] at hi
  unfold radiationPhase
  rw [he]
  have hp' : ‖Complex.exp (Complex.I * ((-k * inner ℝ (n : Position) y : ℝ) : ℂ)) - 1‖ ≤
      |-k * inner ℝ (n : Position) y| := by
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero] using hp
  apply hp'.trans
  rw [abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left hi (abs_nonneg k)

theorem radiationPhase_even_remainder (k : ℝ) (n : UnitSphere) (y : Position) :
    ‖radiationPhase k n y + radiationPhase (-k) n y - 2‖ ≤ k ^ 2 * ‖y‖ ^ 2 := by
  have he : radiationPhase k n y + radiationPhase (-k) n y - 2 =
      ((2 * (Real.cos (k * inner ℝ (n : Position) y) - 1) : ℝ) : ℂ) := by
    rw [SourceTaylor.phase_cos_sin, SourceTaylor.phase_cos_sin]
    simp only [neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hp := SourceTaylor.cos_scalar_remainder (k * inner ℝ (n : Position) y)
  have hi := abs_real_inner_le_norm (n : Position) y
  rw [unitSphere_norm, one_mul] at hi
  have hsq : (inner ℝ (n : Position) y) ^ 2 ≤ ‖y‖ ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ (n : Position) y)) (norm_nonneg y)).mpr hi
    simpa only [sq_abs] using hs
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg k)
  nlinarith only [hp, hm]

theorem radiationField_difference_integral (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤)
    (f : VectorL2) (n : UnitSphere) :
    radiationField k D f n - radiationField 0 D f n =
      ∫ y in D, (radiationPhase k n y - 1) • angularProjection n (f y) := by
  rw [radiationField, radiationField,
    ← integral_sub (radiationIntegrand_integrable k D hfin f n) (radiationIntegrand_integrable 0 D hfin f n)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp [radiationPhase, sub_smul]

theorem radiationField_even_remainder_integral (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤)
    (f : VectorL2) (n : UnitSphere) :
    radiationField k D f n + radiationField (-k) D f n - (2 : ℂ) • radiationField 0 D f n =
      ∫ y in D, (radiationPhase k n y + radiationPhase (-k) n y - 2) • angularProjection n (f y) := by
  unfold radiationField
  rw [← integral_smul,
    ← integral_add (radiationIntegrand_integrable k D hfin f n) (radiationIntegrand_integrable (-k) D hfin f n)]
  have hsum : IntegrableOn (fun y => radiationPhase k n y • angularProjection n (f y) +
      radiationPhase (-k) n y • angularProjection n (f y)) D volume :=
    (radiationIntegrand_integrable k D hfin f n).add (radiationIntegrand_integrable (-k) D hfin f n)
  have hscale : IntegrableOn (fun y => (2 : ℂ) • radiationPhase 0 n y • angularProjection n (f y)) D volume :=
    (radiationIntegrand_integrable 0 D hfin f n).smul (2 : ℂ)
  rw [← integral_sub hsum hscale]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp [radiationPhase, sub_smul, add_smul]

theorem domainRadiationMap_difference_apply_sq (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    ‖(domainRadiationMap k D hD hfin - domainRadiationMap 0 D hD hfin) f‖ ^ 2 ≤
      (|k| * R) ^ 2 * (8 * Real.pi * volume.real D / 3) * ‖f‖ ^ 2 := by
  have hb (n : UnitSphere) (y : Position) (hy : y ∈ D) : ‖radiationPhase k n y - 1‖ ≤ |k| * R := by
    apply (radiationPhase_sub_one_norm_bound k n y).trans
    exact mul_le_mul_of_nonneg_left (by simpa [Metric.mem_closedBall, dist_zero_right] using hsub hy) (abs_nonneg k)
  have h := boundedRadiation_field_square_bound D hD hfin
    (fun n y => radiationPhase k n y - 1) (fun n => (radiationPhase_measurable k n).sub measurable_const)
    (by positivity : 0 ≤ |k| * R) hb (f : VectorL2)
  change ‖domainRadiationMap k D hD hfin f - domainRadiationMap 0 D hD hfin f‖ ^ 2 ≤ _
  rw [← lp_integral_norm_sq sphereArea]
  apply le_trans _ h
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (domainRadiationMap k D hD hfin f) (domainRadiationMap 0 D hD hfin f),
    radiationLp_coe k D hfin (f : VectorL2), radiationLp_coe 0 D hfin (f : VectorL2)] with n hs hk h0
  rw [hs]
  simp only [Pi.sub_apply]
  change ‖radiationLp k D hfin (f : VectorL2) n - radiationLp 0 D hfin (f : VectorL2) n‖ ^ 2 = _
  rw [hk, h0, radiationField_difference_integral k D hfin (f : VectorL2) n]

theorem domainRadiationMap_even_remainder_apply_sq (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    ‖(domainRadiationMap k D hD hfin + domainRadiationMap (-k) D hD hfin -
        (2 : ℂ) • domainRadiationMap 0 D hD hfin) f‖ ^ 2 ≤
      (k ^ 2 * R ^ 2) ^ 2 * (8 * Real.pi * volume.real D / 3) * ‖f‖ ^ 2 := by
  have hb (n : UnitSphere) (y : Position) (hy : y ∈ D) :
      ‖radiationPhase k n y + radiationPhase (-k) n y - 2‖ ≤ k ^ 2 * R ^ 2 := by
    apply (radiationPhase_even_remainder k n y).trans
    have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hsub hy
    have hy2 : ‖y‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg y) hR).mpr hyR
    exact mul_le_mul_of_nonneg_left hy2 (sq_nonneg k)
  have h := boundedRadiation_field_square_bound D hD hfin
    (fun n y => radiationPhase k n y + radiationPhase (-k) n y - 2)
    (fun n => ((radiationPhase_measurable k n).add (radiationPhase_measurable (-k) n)).sub measurable_const)
    (by positivity : 0 ≤ k ^ 2 * R ^ 2) hb (f : VectorL2)
  let a := domainRadiationMap k D hD hfin f
  let b := domainRadiationMap (-k) D hD hfin f
  let c := domainRadiationMap 0 D hD hfin f
  change ‖a + b - (2 : ℂ) • c‖ ^ 2 ≤ _
  rw [← lp_integral_norm_sq sphereArea]
  apply le_trans _ h
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (a + b) ((2 : ℂ) • c), Lp.coeFn_add a b, Lp.coeFn_smul (2 : ℂ) c,
    radiationLp_coe k D hfin (f : VectorL2), radiationLp_coe (-k) D hfin (f : VectorL2),
    radiationLp_coe 0 D hfin (f : VectorL2)] with n hs ha hc hk hm h0
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ha, hc]
  simp only [Pi.add_apply, Pi.smul_apply]
  change ‖radiationLp k D hfin (f : VectorL2) n + radiationLp (-k) D hfin (f : VectorL2) n -
      (2 : ℂ) • radiationLp 0 D hfin (f : VectorL2) n‖ ^ 2 = _
  rw [hk, hm, h0, radiationField_even_remainder_integral k D hfin (f : VectorL2) n]

theorem nonnegative_norm_of_square_bound {x y c C : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (h : x ^ 2 ≤ c ^ 2 * C * y ^ 2) :
    x ≤ Real.sqrt C * c * y := by
  have hs := Real.sq_sqrt hC
  have heq : (Real.sqrt C * c * y) ^ 2 = c ^ 2 * C * y ^ 2 := by rw [mul_pow, mul_pow, hs]; ring
  nlinarith only [h, heq, _hx, mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) hc) hy]

theorem domainRadiationMap_difference_apply_norm_le (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    ‖(domainRadiationMap k D hD hfin - domainRadiationMap 0 D hD hfin) f‖ ≤
      Real.sqrt (8 * Real.pi * volume.real D / 3) * (|k| * R) * ‖f‖ :=
  nonnegative_norm_of_square_bound (norm_nonneg _) (norm_nonneg _) (by positivity) (by positivity)
    (domainRadiationMap_difference_apply_sq k D hD hfin hR hsub f)

theorem domainRadiationMap_even_remainder_apply_norm_le (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    ‖(domainRadiationMap k D hD hfin + domainRadiationMap (-k) D hD hfin -
        (2 : ℂ) • domainRadiationMap 0 D hD hfin) f‖ ≤
      Real.sqrt (8 * Real.pi * volume.real D / 3) * (k ^ 2 * R ^ 2) * ‖f‖ :=
  nonnegative_norm_of_square_bound (norm_nonneg _) (norm_nonneg _) (by positivity) (by positivity)
    (domainRadiationMap_even_remainder_apply_sq k D hD hfin hR hsub f)

end QuarticMaxwell
