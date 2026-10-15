import QuarticMaxwell.SupportedOperators
import QuarticMaxwell.SourceTaylor
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual complete-angle radiation Gram operator, exact antipodal
evenness, and its zero-frequency moment identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem linear_inner_of_norm_sq {H E G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (A : H →ₗ[ℂ] E) (B : H →ₗ[ℂ] G) (c : ℝ)
    (h : ∀ u, ‖A u‖ ^ 2 = c * ‖B u‖ ^ 2) (u v : H) :
    inner ℂ (A u) (A v) = (c : ℂ) * inner ℂ (B u) (B v) := by
  have hp := h (u + v)
  have hm := h (u - v)
  have hpi := h (u + Complex.I • v)
  have hmi := h (u - Complex.I • v)
  simp only [map_add, map_sub, map_smul] at hp hm hpi hmi
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change RCLike.re (inner ℂ (A u) (A v)) = c * RCLike.re (inner ℂ (B u) (B v))
    rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ),
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)]
    nlinarith only [hp, hm]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change RCLike.im (inner ℂ (A u) (A v)) = c * RCLike.im (inner ℂ (B u) (B v))
    rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ),
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ)]
    change (‖A u - Complex.I • A v‖ * ‖A u - Complex.I • A v‖ -
        ‖A u + Complex.I • A v‖ * ‖A u + Complex.I • A v‖) / 4 =
      c * ((‖B u - Complex.I • B v‖ * ‖B u - Complex.I • B v‖ -
        ‖B u + Complex.I • B v‖ * ‖B u + Complex.I • B v‖) / 4)
    nlinarith only [hpi, hmi]

def sphereAntipode : UnitSphere ≃ₜ UnitSphere :=
  orthogonalSphere (LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position)

theorem sphereAntipode_coe (n : UnitSphere) : ((sphereAntipode n : UnitSphere) : Position) = -(n : Position) := rfl

theorem angularProjection_antipode (n : UnitSphere) :
    angularProjection (sphereAntipode n) = angularProjection n := by
  ext v i
  simp [angularProjection, sphereAntipode_coe, complexify, PiLp.inner_apply,
    RCLike.inner_apply, InnerProductSpace.rankOne_apply, PiLp.smul_apply, PiLp.sub_apply]
  ring

theorem radiationPhase_antipode (k : ℝ) (n : UnitSphere) (y : Position) :
    radiationPhase k (sphereAntipode n) y = radiationPhase (-k) n y := by
  unfold radiationPhase
  rw [sphereAntipode_coe, inner_neg_left]
  congr 2
  push_cast
  ring

theorem radiationField_antipode (k : ℝ) (D : Set Position) (f : VectorL2) (n : UnitSphere) :
    radiationField k D f (sphereAntipode n) = radiationField (-k) D f n := by
  unfold radiationField
  simp only [radiationPhase_antipode, angularProjection_antipode]

theorem domainRadiationMap_norm_sq_even (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) (f : DomainL2 D) :
    ‖domainRadiationMap (-k) D hD hfin f‖ ^ 2 = ‖domainRadiationMap k D hD hfin f‖ ^ 2 := by
  have hlp (t : ℝ) : ‖domainRadiationMap t D hD hfin f‖ ^ 2 =
      ∫ n : UnitSphere, ‖radiationField t D (f : VectorL2) n‖ ^ 2 ∂sphereArea := by
    rw [← lp_integral_norm_sq sphereArea]
    apply integral_congr_ae
    filter_upwards [radiationLp_coe t D hfin (f : VectorL2)] with n hn
    change ‖radiationLp t D hfin (f : VectorL2) n‖ ^ 2 = _
    rw [hn]
  rw [hlp, hlp]
  have h := sphere_integral_orthogonal (LinearIsometryEquiv.neg ℝ : Position ≃ₗᵢ[ℝ] Position)
    (fun n => ‖radiationField k D (f : VectorL2) n‖ ^ 2)
  change (∫ n : UnitSphere, ‖radiationField k D (f : VectorL2) (sphereAntipode n)‖ ^ 2 ∂sphereArea) = _ at h
  simpa only [radiationField_antipode] using h

def radiationGram (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) : DomainL2 D →L[ℂ] DomainL2 D := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  exact (((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ)) •
    ((domainRadiationMap k D hD hfin).adjoint ∘L domainRadiationMap k D hD hfin)

theorem radiationGram_inner (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (p q : DomainL2 D) :
    inner ℂ p (radiationGram k D hD hfin q) =
      (((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ)) *
        inner ℂ (domainRadiationMap k D hD hfin p) (domainRadiationMap k D hD hfin q) := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  change inner ℂ p ((((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ)) •
    (domainRadiationMap k D hD hfin).adjoint (domainRadiationMap k D hD hfin q)) = _
  calc
    _ = (((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ)) *
        inner ℂ p ((domainRadiationMap k D hD hfin).adjoint (domainRadiationMap k D hD hfin q)) :=
      inner_smul_right p _ _
    _ = _ := by rw [ContinuousLinearMap.adjoint_inner_right]

theorem radiationGram_even (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) : radiationGram (-k) D hD hfin = radiationGram k D hD hfin := by
  have he (p q : DomainL2 D) :
      inner ℂ (domainRadiationMap (-k) D hD hfin p) (domainRadiationMap (-k) D hD hfin q) =
        inner ℂ (domainRadiationMap k D hD hfin p) (domainRadiationMap k D hD hfin q) := by
    have h := linear_inner_of_norm_sq (domainRadiationMap (-k) D hD hfin).toLinearMap
      (domainRadiationMap k D hD hfin).toLinearMap 1
      (fun p => by simpa using domainRadiationMap_norm_sq_even k D hD hfin p) p q
    simpa using h
  apply ContinuousLinearMap.ext
  intro q
  apply ext_inner_left ℂ
  intro p
  rw [radiationGram_inner, radiationGram_inner, he]

def supportMomentLinear (D : Set Position) (hfin : volume D ≠ ⊤) : DomainL2 D →ₗ[ℂ] Vector where
  toFun p := ∫ y in D, (p : VectorL2) y
  map_add' p q := by
    calc
      _ = ∫ y in D, ((p : VectorL2) y + (q : VectorL2) y) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (p : VectorL2) (q : VectorL2))] with y hy
        exact hy
      _ = _ := integral_add
        (integrableOn_Lp_of_measure_ne_top (p : VectorL2) (by norm_num) hfin)
        (integrableOn_Lp_of_measure_ne_top (q : VectorL2) (by norm_num) hfin)
  map_smul' z p := by
    change (∫ y in D, ((z • p : DomainL2 D) : VectorL2) y) = z • _
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul z (p : VectorL2))] with y hy
    exact hy

theorem radiationField_zero_moment (D : Set Position) (hfin : volume D ≠ ⊤)
    (p : DomainL2 D) (n : UnitSphere) :
    radiationField 0 D (p : VectorL2) n = angularProjection n (supportMomentLinear D hfin p) := by
  unfold radiationField
  simp only [radiationPhase, zero_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_smul]
  exact (angularProjection n).integral_comp_comm
    (integrableOn_Lp_of_measure_ne_top (p : VectorL2) (by norm_num) hfin)

theorem domainRadiationMap_zero_norm_sq (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (p : DomainL2 D) :
    ‖domainRadiationMap 0 D hD hfin p‖ ^ 2 = 8 * Real.pi / 3 * ‖supportMomentLinear D hfin p‖ ^ 2 := by
  rw [← lp_integral_norm_sq sphereArea]
  calc
    _ = ∫ n : UnitSphere, ‖angularProjection n (supportMomentLinear D hfin p)‖ ^ 2 ∂sphereArea := by
      apply integral_congr_ae
      filter_upwards [radiationLp_coe 0 D hfin (p : VectorL2)] with n hn
      change ‖radiationLp 0 D hfin (p : VectorL2) n‖ ^ 2 = _
      rw [hn, radiationField_zero_moment]
    _ = _ := angularProjection_integral _

theorem radiationGram_zero_moment (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (p q : DomainL2 D) :
    inner ℂ p (radiationGram 0 D hD hfin q) =
      (((1 / (6 * Real.pi) : ℝ) : ℂ)) *
        inner ℂ (supportMomentLinear D hfin p) (supportMomentLinear D hfin q) := by
  have h := linear_inner_of_norm_sq (domainRadiationMap 0 D hD hfin).toLinearMap
    (supportMomentLinear D hfin) (8 * Real.pi / 3) (domainRadiationMap_zero_norm_sq D hD hfin) p q
  change inner ℂ (domainRadiationMap 0 D hD hfin p) (domainRadiationMap 0 D hD hfin q) =
    (((8 * Real.pi / 3 : ℝ) : ℂ)) * inner ℂ (supportMomentLinear D hfin p) (supportMomentLinear D hfin q) at h
  rw [radiationGram_inner, h]
  push_cast
  field_simp
  ring

theorem constantSource_inner_moment (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (e : Vector) (q : DomainL2 D) :
    inner ℂ (SourceTaylor.constantSource D hD hfin e) q =
      inner ℂ e (supportMomentLinear D hfin q) := by
  change inner ℂ (SourceTaylor.constantSource D hD hfin e : VectorL2) (q : VectorL2) = _
  rw [L2.inner_def]
  calc
    _ = ∫ y in D, inner ℂ e ((q : VectorL2) y) := by
      rw [← integral_indicator hD]
      apply integral_congr_ae
      filter_upwards [SourceTaylor.constantSource_coe D hD hfin e] with y hy
      rw [hy]
      by_cases hd : y ∈ D <;> simp [hd]
    _ = _ := integral_inner
      (integrableOn_Lp_of_measure_ne_top (q : VectorL2) (by norm_num) hfin) e

end QuarticMaxwell
