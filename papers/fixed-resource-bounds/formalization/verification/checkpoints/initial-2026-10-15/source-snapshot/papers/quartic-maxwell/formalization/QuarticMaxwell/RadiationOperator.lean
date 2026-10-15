import QuarticMaxwell.RadiationMoment
import QuarticMaxwell.SquareIntegral
import PrescribedExtinction.SetSupportedL2

/-! The complete vector radiation transform on an arbitrary finite-volume
measurable support. Its `8πV/3` squared norm is derived from source
Cauchy--Schwarz and the exact sphere projection moment. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

def radiationPhase (k : ℝ) (n : UnitSphere) (y : Position) : ℂ :=
  Complex.exp (-Complex.I * ((k * inner ℝ (n : Position) y : ℝ) : ℂ))

theorem radiationPhase_norm (k : ℝ) (n : UnitSphere) (y : Position) :
    ‖radiationPhase k n y‖ = 1 := by simp [radiationPhase, Complex.norm_exp]

theorem radiationPhase_measurable (k : ℝ) (n : UnitSphere) : Measurable (radiationPhase k n) := by
  unfold radiationPhase
  fun_prop

theorem angularProjection_continuous : Continuous angularProjection := by
  have h := rankOne_complexify_continuous.comp
    (continuous_subtype_val : Continuous (fun n : UnitSphere => (n : Position)))
  exact continuous_const.sub h

theorem angularProjection_apply_norm_le (n : UnitSphere) (v : Vector) :
    ‖angularProjection n v‖ ≤ ‖v‖ := by
  have h := angularProjection_pythagoras n v
  nlinarith [norm_nonneg (angularProjection n v), norm_nonneg v,
    sq_nonneg ‖inner ℂ (complexify n) v‖]

def radiationField (k : ℝ) (D : Set Position) (f : VectorL2) (n : UnitSphere) : Vector :=
  ∫ y in D, radiationPhase k n y • angularProjection n (f y)

theorem radiationIntegrand_norm_le (k : ℝ) (f : VectorL2) (n : UnitSphere) (y : Position) :
    ‖radiationPhase k n y • angularProjection n (f y)‖ ≤ ‖f y‖ := by
  rw [norm_smul, radiationPhase_norm, one_mul]
  exact angularProjection_apply_norm_le n (f y)

theorem radiationIntegrand_memLp (k : ℝ) (D : Set Position) (f : VectorL2) (n : UnitSphere) :
    MemLp (fun y => radiationPhase k n y • angularProjection n (f y)) 2 (volume.restrict D) := by
  have hm := (radiationPhase_measurable k n).aestronglyMeasurable.smul
    ((angularProjection n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  exact ((Lp.memLp f).restrict D).of_le hm.restrict
    (ae_of_all _ (radiationIntegrand_norm_le k f n))

theorem radiationIntegrand_integrable (k : ℝ) (D : Set Position)
    (hfin : volume D ≠ ⊤) (f : VectorL2) (n : UnitSphere) :
    IntegrableOn (fun y => radiationPhase k n y • angularProjection n (f y)) D volume := by
  have hi : IntegrableOn (fun y => f y) D volume :=
    integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin
  apply Integrable.mono' hi.norm (radiationIntegrand_memLp k D f n).aestronglyMeasurable
  exact ae_of_all _ (radiationIntegrand_norm_le k f n)

theorem radiationField_continuous (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤)
    (f : VectorL2) : Continuous (radiationField k D f) := by
  have hi : IntegrableOn (fun y => f y) D volume :=
    integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin
  apply continuous_of_dominated (bound := fun y => ‖f y‖)
  · intro n
    exact (radiationIntegrand_memLp k D f n).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (radiationIntegrand_norm_le k f n)
  · exact hi.norm
  · exact ae_of_all _ fun y => by
      have hp := angularProjection_continuous
      unfold radiationPhase
      fun_prop

theorem radiationField_memLp (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤)
    (f : VectorL2) : MemLp (radiationField k D f) 2 sphereArea := by
  have hi : IntegrableOn (fun y => f y) D volume :=
    integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin
  apply MemLp.of_bound (radiationField_continuous k D hfin f).aestronglyMeasurable
    (∫ y in D, ‖f y‖)
  exact ae_of_all _ fun n =>
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
        hi.norm (ae_of_all _ (radiationIntegrand_norm_le k f n)))

theorem radiationField_pointwise_square_bound (k : ℝ) (D : Set Position)
    (_hD : MeasurableSet D) (hfin : volume D ≠ ⊤) (f : VectorL2) (n : UnitSphere) :
    ‖radiationField k D f n‖ ^ 2 ≤
      volume.real D * (∫ y in D, ‖angularProjection n (f y)‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin.lt_top⟩
  have h := norm_integral_sq_le_measure_mul_square (volume.restrict D)
    (fun y => radiationPhase k n y • angularProjection n (f y)) (radiationIntegrand_memLp k D f n)
  simpa [radiationField, norm_smul, radiationPhase_norm, Measure.real] using h

theorem projection_square_joint_integrable (D : Set Position) (f : VectorL2) :
    Integrable (fun z : UnitSphere × Position => ‖angularProjection z.1 (f z.2)‖ ^ 2)
      (sphereArea.prod (volume.restrict D)) := by
  have hf₂ : Integrable (fun y : Position => ‖f y‖ ^ 2) (volume.restrict D) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f).restrict).mp ((Lp.memLp f).restrict D)
  have hdom : Integrable (fun z : UnitSphere × Position => (1 : ℝ) * ‖f z.2‖ ^ 2)
      (sphereArea.prod (volume.restrict D)) := (integrable_const 1).mul_prod hf₂
  have happ : AEStronglyMeasurable (fun z : UnitSphere × Position => angularProjection z.1 (f z.2))
      (sphereArea.prod (volume.restrict D)) :=
    (ContinuousLinearMap.id ℂ (Vector →L[ℂ] Vector)).aestronglyMeasurable_comp₂
    angularProjection_continuous.aestronglyMeasurable.comp_fst
    (Lp.aestronglyMeasurable f).restrict.comp_snd
  apply Integrable.mono' hdom (happ.norm.pow 2)
  exact ae_of_all _ fun z => by
    change ‖‖angularProjection z.1 (f z.2)‖ ^ 2‖ ≤ 1 * ‖f z.2‖ ^ 2
    have h := angularProjection_apply_norm_le z.1 (f z.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), one_mul]
    nlinarith [norm_nonneg (angularProjection z.1 (f z.2)), norm_nonneg (f z.2)]

theorem radiationField_square_bound (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) (f : VectorL2) :
    (∫ n : UnitSphere, ‖radiationField k D f n‖ ^ 2 ∂sphereArea) ≤
      8 * Real.pi * volume.real D / 3 * ‖f‖ ^ 2 := by
  have hj := projection_square_joint_integrable D f
  have hf₂ : Integrable (fun y : Position => ‖f y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hbound : (∫ n : UnitSphere, ‖radiationField k D f n‖ ^ 2 ∂sphereArea) ≤
      volume.real D * (∫ n : UnitSphere, (∫ y in D,
        ‖angularProjection n (f y)‖ ^ 2) ∂sphereArea) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ fun n => sq_nonneg _
    · exact hj.integral_prod_left.const_mul (volume.real D)
    · exact ae_of_all _ (radiationField_pointwise_square_bound k D hD hfin f)
  have hswap : (∫ n : UnitSphere, (∫ y in D,
      ‖angularProjection n (f y)‖ ^ 2) ∂sphereArea) =
      8 * Real.pi / 3 * (∫ y in D, ‖f y‖ ^ 2) := by
    rw [integral_integral_swap hj]
    simp only [angularProjection_integral, integral_const_mul]
  rw [hswap] at hbound
  have hsource : (∫ y in D, ‖f y‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    rw [← lp_integral_norm_sq volume f]
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun y => sq_nonneg _) hf₂
  apply hbound.trans
  have hmul := mul_le_mul_of_nonneg_left hsource
    (show 0 ≤ volume.real D * (8 * Real.pi / 3) by positivity)
  nlinarith

theorem radiationField_add (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤)
    (f g : VectorL2) : radiationField k D (f + g) = radiationField k D f + radiationField k D g := by
  funext n
  unfold radiationField
  calc
    _ = ∫ y in D, (radiationPhase k n y • angularProjection n (f y) +
        radiationPhase k n y • angularProjection n (g y)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_add f g)] with y hy
      rw [hy]
      simp only [Pi.add_apply, map_add, smul_add]
    _ = _ := integral_add (radiationIntegrand_integrable k D hfin f n)
      (radiationIntegrand_integrable k D hfin g n)

theorem radiationField_smul (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤)
    (z : ℂ) (f : VectorL2) : radiationField k D (z • f) = z • radiationField k D f := by
  funext n
  unfold radiationField
  simp only [Pi.smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul z f)] with y hy
  rw [hy]
  simp only [Pi.smul_apply, map_smul]
  exact smul_comm _ _ _

def radiationLp (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤) (f : VectorL2) :
    Lp Vector 2 sphereArea := (radiationField_memLp k D hfin f).toLp (radiationField k D f)

theorem radiationLp_coe (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤) (f : VectorL2) :
    radiationLp k D hfin f =ᵐ[sphereArea] radiationField k D f :=
  (radiationField_memLp k D hfin f).coeFn_toLp

def radiationLinear (k : ℝ) (D : Set Position) (hfin : volume D ≠ ⊤) :
    VectorL2 →ₗ[ℂ] Lp Vector 2 sphereArea where
  toFun := radiationLp k D hfin
  map_add' f g := by
    change radiationLp k D hfin (f + g) = radiationLp k D hfin f + radiationLp k D hfin g
    apply Lp.ext
    filter_upwards [radiationLp_coe k D hfin (f + g), radiationLp_coe k D hfin f,
      radiationLp_coe k D hfin g, Lp.coeFn_add (radiationLp k D hfin f) (radiationLp k D hfin g)] with n hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply]
    rw [hf, hg]
    exact congrFun (radiationField_add k D hfin f g) n
  map_smul' z f := by
    change radiationLp k D hfin (z • f) = z • radiationLp k D hfin f
    apply Lp.ext
    filter_upwards [radiationLp_coe k D hfin (z • f), radiationLp_coe k D hfin f,
      Lp.coeFn_smul z (radiationLp k D hfin f)] with n hzf hf ha
    rw [hzf, ha]
    simp only [Pi.smul_apply]
    rw [hf]
    exact congrFun (radiationField_smul k D hfin z f) n

theorem radiationLp_norm_sq_bound (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (f : VectorL2) :
    ‖radiationLp k D hfin f‖ ^ 2 ≤ 8 * Real.pi * volume.real D / 3 * ‖f‖ ^ 2 := by
  have h := radiationField_square_bound k D hD hfin f
  rw [← lp_integral_norm_sq sphereArea (radiationLp k D hfin f)]
  apply le_trans _ h
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [radiationLp_coe k D hfin f] with n hn
  rw [hn]

theorem radiationLinear_bound (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (f : VectorL2) :
    ‖radiationLinear k D hfin f‖ ≤ Real.sqrt (8 * Real.pi * volume.real D / 3) * ‖f‖ := by
  have h := radiationLp_norm_sq_bound k D hD hfin f
  have hs := Real.sq_sqrt (show 0 ≤ 8 * Real.pi * volume.real D / 3 by positivity)
  change ‖radiationLp k D hfin f‖ ≤ _
  have hsq : ‖radiationLp k D hfin f‖ ^ 2 ≤
      (Real.sqrt (8 * Real.pi * volume.real D / 3) * ‖f‖) ^ 2 := by
    rw [mul_pow, hs]
    exact h
  nlinarith [norm_nonneg (radiationLp k D hfin f),
    mul_nonneg (Real.sqrt_nonneg (8 * Real.pi * volume.real D / 3)) (norm_nonneg f)]

def radiationMap (k : ℝ) (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    VectorL2 →L[ℂ] Lp Vector 2 sphereArea :=
  (radiationLinear k D hfin).mkContinuous (Real.sqrt (8 * Real.pi * volume.real D / 3))
    (radiationLinear_bound k D hD hfin)

/-- The manuscript's exact complete-radiation squared operator norm. -/
theorem radiationMap_norm_sq_le (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) : ‖radiationMap k D hD hfin‖ ^ 2 ≤ 8 * Real.pi * volume.real D / 3 := by
  have h := LinearMap.mkContinuous_norm_le (radiationLinear k D hfin)
    (Real.sqrt_nonneg (8 * Real.pi * volume.real D / 3)) (radiationLinear_bound k D hD hfin)
  have hs := Real.sq_sqrt (show 0 ≤ 8 * Real.pi * volume.real D / 3 by positivity)
  change ‖radiationMap k D hD hfin‖ ≤ _ at h
  nlinarith [norm_nonneg (radiationMap k D hD hfin)]

end QuarticMaxwell
