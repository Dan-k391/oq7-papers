import QuarticMaxwell.HomogeneousCoefficient
import QuarticMaxwell.SharpnessClass

/-! Bounds depending only on the material and the fixed relative sphere size,
uniform over every real unit direction and transverse polarization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed FixedPatternWork FixedPatternScattering MeasureTheory

def referenceVolume (a : ℝ) : ℝ := 12 * Real.pi * a ^ 3
def responseCorrection (μ a : ℝ) : ℝ := 3 / 4 * μ ^ 2 * volumeRadius (referenceVolume a) ^ 2
def forwardErrorBound (μ a : ℝ) : ℝ :=
  referenceVolume a * (2 * μ * (3 / 5 : ℝ) ^ 2 + responseCorrection μ a)
def scatteringErrorBound (μ a : ℝ) : ℝ :=
  4 * referenceVolume a *
    ((μ * (3 / 5 : ℝ) ^ 2 / 2 + responseCorrection μ a) * (referenceVolume a / (6 * Real.pi)) * μ * (3 / 5) +
      μ ^ 2 * (referenceVolume a * (3 / 5 : ℝ) ^ 2 / (3 * Real.pi)) * (3 / 5) +
      μ * (referenceVolume a / (6 * Real.pi)) * (μ * (3 / 5 : ℝ) ^ 3 / 6 + responseCorrection μ a * (3 / 5)))
def leadingBound (μ a : ℝ) : ℝ :=
  (2 / (3 * Real.pi)) * (μ * referenceVolume a) * ((3 / 5 : ℝ) * μ * referenceVolume a)

theorem Parameters.rho_eq (P : Parameters) : rho P.body = P.μ := by
  change P.material.cap ^ 2 / P.material.loss = P.μ
  rw [Parameters.material, TwoSupportBounds.homogeneous_cap, TwoSupportBounds.homogeneous_loss]
  field_simp [P.μ_pos.ne']

theorem Parameters.input_norm_sq (P : Parameters) :
    ‖constantInput P.body P.electric‖ ^ 2 = referenceVolume P.a := by
  change ‖P.f0‖ ^ 2 = _
  rw [P.f0_norm, Real.sq_sqrt measureReal_nonneg, P.body_volume]
  rfl

theorem Parameters.correction_eq (P : Parameters) :
    correction P.body = responseCorrection P.μ P.a := by
  rw [correction, P.rho_eq, P.body_volume]
  rfl

theorem Parameters.forwardError_eq (P : Parameters) :
    FixedPatternContrast.denominatorError P.body P.electric = forwardErrorBound P.μ P.a := by
  unfold FixedPatternContrast.denominatorError forwardErrorBound
  rw [P.input_norm_sq, P.rho_eq, P.correction_eq]
  rfl

theorem Parameters.scatteringError_eq (P : Parameters) :
    errorConstant P.body P.electric = scatteringErrorBound P.μ P.a := by
  unfold errorConstant scatteringErrorBound gramBound gramCorrection
  rw [P.input_norm_sq, P.rho_eq, P.correction_eq, P.body_volume]
  rfl

theorem Parameters.p0_norm (P : Parameters) : ‖P.p0‖ ≤ P.μ * referenceVolume P.a := by
  have h := MomentOperator.norm_le P.body.domain P.body.finite (staticResponse P.body P.f0)
  change ‖P.p0‖ ≤ Real.sqrt (volume.real P.body.domain) * ‖staticResponse P.body P.f0‖ at h
  calc
    _ ≤ Real.sqrt (volume.real P.body.domain) * (P.μ * ‖P.f0‖) :=
      h.trans (mul_le_mul_of_nonneg_left
        (((staticResponse P.body).le_opNorm P.f0).trans
          (mul_le_mul_of_nonneg_right P.static_norm (norm_nonneg _))) (Real.sqrt_nonneg _))
    _ = _ := by rw [P.f0_norm]; rw [mul_left_comm, ← pow_two, Real.sq_sqrt measureReal_nonneg, P.body_volume]; rfl

theorem Parameters.leading_bound (P : Parameters) :
    |leading P.body P.n P.electric| ≤ leadingBound P.μ P.a := by
  change |(2 / (3 * Real.pi)) * (inner ℂ P.p0 P.p1).im| ≤ _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (3 * Real.pi))]
  calc
    _ ≤ (2 / (3 * Real.pi)) * (‖P.p0‖ * ‖P.p1‖) :=
      mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)) (by positivity)
    _ ≤ (2 / (3 * Real.pi)) * ((P.μ * referenceVolume P.a) *
        ((3 / 5 : ℝ) * P.μ * referenceVolume P.a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul P.p0_norm _ (norm_nonneg _) (by unfold referenceVolume; positivity [P.μ_pos, P.a_pos])
      · convert P.p1_norm using 1
        unfold referenceVolume
        ring
    _ = _ := by unfold leadingBound; ring

def denominatorFloor (μ a : ℝ) : ℝ := μ * referenceVolume a / (1 + μ) ^ 2
def remainderBound (μ a : ℝ) : ℝ :=
  2 * scatteringErrorBound μ a / denominatorFloor μ a +
    2 * leadingBound μ a * forwardErrorBound μ a / (denominatorFloor μ a) ^ 2
def intervalFloor (μ a : ℝ) : ℝ :=
  Real.sqrt (denominatorFloor μ a / (2 * (forwardErrorBound μ a + 1)))
def uniformCutoff (μ a : ℝ) : ℝ :=
  min 1 (min (intervalFloor μ a)
    (Real.sqrt (coefficientFloor μ a / (2 * (remainderBound μ a + 1)))))

theorem data_nonnegative {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 ≤ forwardErrorBound μ a ∧ 0 ≤ scatteringErrorBound μ a ∧ 0 ≤ leadingBound μ a := by
  have hv : 0 < referenceVolume a := by unfold referenceVolume; positivity
  have hc : 0 ≤ responseCorrection μ a := by unfold responseCorrection; positivity
  unfold forwardErrorBound scatteringErrorBound leadingBound
  constructor
  · positivity
  constructor <;> positivity

theorem denominatorFloor_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 < denominatorFloor μ a := by
  unfold denominatorFloor referenceVolume
  positivity

theorem remainderBound_nonneg {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 ≤ remainderBound μ a := by
  have hd := (denominatorFloor_pos hμ ha).le
  obtain ⟨he, hs, hl⟩ := data_nonnegative hμ ha
  unfold remainderBound
  positivity

theorem uniformCutoff_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 < uniformCutoff μ a := by
  have hd := denominatorFloor_pos hμ ha
  have he := (data_nonnegative hμ ha).1
  have hK := remainderBound_nonneg hμ ha
  have hC := coefficientFloor_pos hμ ha
  unfold uniformCutoff intervalFloor
  exact lt_min (by norm_num) (lt_min
    (Real.sqrt_pos.mpr (div_pos hd (by positivity)))
    (Real.sqrt_pos.mpr (div_pos hC (by positivity))))

theorem Parameters.interval_lower (P : Parameters)
    (hD : denominatorFloor P.μ P.a ≤ D0 P.body P.electric) :
    intervalFloor P.μ P.a ≤ FixedPatternContrast.interval P.body P.electric := by
  unfold intervalFloor FixedPatternContrast.interval
  rw [P.forwardError_eq]
  have he := (data_nonnegative P.μ_pos P.a_pos).1
  gcongr

theorem Parameters.remainder_nonneg (P : Parameters) :
    0 ≤ FixedPatternContrast.remainderConstant P.body P.n P.electric := by
  have hv : 0 < volume.real P.body.domain := by rw [P.body_volume]; positivity [P.a_pos]
  have hd := D0_pos P.body hv P.n P.electric P.electric_norm
  have he := errorConstant_nonneg P.body P.electric
  have hf := FixedPatternContrast.denominatorError_nonneg P.body P.electric
  unfold FixedPatternContrast.remainderConstant
  positivity

theorem Parameters.remainder_upper (P : Parameters)
    (hD : denominatorFloor P.μ P.a ≤ D0 P.body P.electric) :
    FixedPatternContrast.remainderConstant P.body P.n P.electric ≤ remainderBound P.μ P.a := by
  have hd := denominatorFloor_pos P.μ_pos P.a_pos
  obtain ⟨he, hs, hl⟩ := data_nonnegative P.μ_pos P.a_pos
  unfold FixedPatternContrast.remainderConstant remainderBound
  rw [P.forwardError_eq, P.scatteringError_eq]
  apply add_le_add
  · exact div_le_div₀ (by positivity) le_rfl hd hD
  · apply div_le_div₀ (by positivity) _ (sq_pos_of_pos hd)
      ((sq_le_sq₀ hd.le (hd.trans_le hD).le).mpr hD)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left P.leading_bound (by norm_num)) he

theorem Parameters.electric_real (P : Parameters) : vectorConjugate P.electric = P.electric := by
  ext i
  simp [Parameters.electric, vectorConjugate, complexify]

theorem Parameters.electric_transverse (P : Parameters) :
    bilinear (complexify (P.n : Position)) P.electric = 0 := by
  rw [bilinear_complexify_eq_inner, Parameters.electric, ← axisCoupling_eq_inner,
    axisCoupling_complexify_inner, P.transverse]
  rfl

theorem Parameters.uniform_physical_lower (P : Parameters)
    (hD : denominatorFloor P.μ P.a ≤ D0 P.body P.electric)
    (hC : coefficientFloor P.μ P.a ≤ FixedPatternContrast.coefficient P.body P.n P.electric)
    (k r : ℝ) (hk : 0 < k) (hr : 0 < r) (hsmall : k * r ≤ uniformCutoff P.μ P.a)
    (s : WeakMaterial.State (PhysicalDilation.medium P.body r hr) k P.n P.electric)
    (q : WeakMaterial.State (PhysicalDilation.medium P.body r hr) k (PhysicalPowers.opposite P.n) P.electric) :
    coefficientFloor P.μ P.a / 2 * (k * r) ^ 4 ≤
      FixedPatternContrast.contrast (PhysicalDilation.medium P.body r hr) k P.n P.electric s q := by
  have hv : 0 < volume.real P.body.domain := by rw [P.body_volume]; positivity [P.a_pos]
  have hs : SharpnessClass.Reciprocal P.body :=
    TwoSphereGeometry.medium_reciprocal P.n P.a P.a_pos P.a_small P.material
  have hI : k * r ≤ FixedPatternContrast.interval P.body P.electric :=
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))).trans (P.interval_lower hD)
  have herr := FixedPatternDilation.fixed_wavenumber_quartic P.body hv hs k hk P.n P.electric
    P.electric_real P.electric_norm P.electric_transverse r hr
    ((le_div_iff₀ hk).mpr (by nlinarith [hI])) s q
  have hK := P.remainder_upper hD
  have herr' := herr.trans (mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ (k * r) ^ 6))
  have hroot : k * r ≤ Real.sqrt (coefficientFloor P.μ P.a / (2 * (remainderBound P.μ P.a + 1))) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht := mul_pos hk hr
  have hK0 := remainderBound_nonneg P.μ_pos P.a_pos
  have hC0 := coefficientFloor_pos P.μ_pos P.a_pos
  have hsq := (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).mpr hroot
  rw [Real.sq_sqrt (by positivity)] at hsq
  have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (remainderBound P.μ P.a + 1))).mp hsq
  have hsmallK : remainderBound P.μ P.a * (k * r) ^ 2 ≤ coefficientFloor P.μ P.a / 2 := by
    nlinarith [sq_nonneg (k * r)]
  exact positive_coefficient_lower_bound ht.le hC hK0 herr' hsmallK

end QuarticMaxwell.HomogeneousMoments
