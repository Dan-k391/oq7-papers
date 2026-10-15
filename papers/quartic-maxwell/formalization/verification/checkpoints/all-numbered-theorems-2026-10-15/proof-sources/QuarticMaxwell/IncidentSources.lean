import QuarticMaxwell.RadiationOperator

/-! Genuine opposite plane-wave sources on the same measurable support.
Their source norms and difference estimate are derived from the complex
exponential, rather than supplied as operator-model assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

def incidentWave (k : ℝ) (n : UnitSphere) (e : Vector) (x : Position) : Vector :=
  radiationPhase k n x • e

theorem incidentWave_norm (k : ℝ) (n : UnitSphere) (e : Vector) (x : Position) :
    ‖incidentWave k n e x‖ = ‖e‖ := by
  simp [incidentWave, norm_smul, radiationPhase_norm]

theorem purePhase_difference_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have he : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    have hh : Complex.I * (b : ℂ) + Complex.I * ((a - b : ℝ) : ℂ) = Complex.I * (a : ℂ) := by
      push_cast
      ring
    rw [hh, mul_one]
  rw [he, norm_mul,
    show ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 by simp [Complex.norm_exp], one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem incidentWave_opposite_difference (k : ℝ) (hk : 0 ≤ k) (n : UnitSphere)
    (e : Vector) (x : Position) :
    ‖incidentWave k n e x - incidentWave (-k) n e x‖ ≤ 2 * k * ‖x‖ * ‖e‖ := by
  have hn : ‖(n : Position)‖ = 1 := (mem_sphere_zero_iff_norm).mp n.property
  have hp := purePhase_difference_le (-k * inner ℝ (n : Position) x)
    (k * inner ℝ (n : Position) x)
  have hphase : ‖radiationPhase k n x - radiationPhase (-k) n x‖ ≤
      2 * k * ‖x‖ := by
    have he₁ : -Complex.I * ((k * inner ℝ (n : Position) x : ℝ) : ℂ) =
        Complex.I * ((-k * inner ℝ (n : Position) x : ℝ) : ℂ) := by push_cast; ring
    have he₂ : -Complex.I * (((-k) * inner ℝ (n : Position) x : ℝ) : ℂ) =
        Complex.I * ((k * inner ℝ (n : Position) x : ℝ) : ℂ) := by push_cast; ring
    unfold radiationPhase
    rw [he₁, he₂]
    apply hp.trans
    have hi := abs_real_inner_le_norm (n : Position) x
    rw [hn, one_mul] at hi
    have he : -k * inner ℝ (n : Position) x - k * inner ℝ (n : Position) x =
        (-2 * k) * inner ℝ (n : Position) x := by ring
    rw [he, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hk]
    nlinarith
  rw [incidentWave, incidentWave, ← sub_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right hphase (norm_nonneg e)

theorem incidentSource_memLp (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    MemLp (D.indicator (incidentWave k n e)) 2 volume := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin.lt_top⟩
  rw [memLp_indicator_iff_restrict hD]
  apply MemLp.of_bound
    (((radiationPhase_measurable k n).aestronglyMeasurable.smul_const e).restrict) ‖e‖
  exact ae_of_all _ fun x => (incidentWave_norm k n e x).le

def incidentSource (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) : VectorL2 :=
  (incidentSource_memLp k n e D hD hfin).toLp (D.indicator (incidentWave k n e))

theorem incidentSource_coe (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    incidentSource k n e D hD hfin =ᵐ[volume] D.indicator (incidentWave k n e) :=
  (incidentSource_memLp k n e D hD hfin).coeFn_toLp

theorem incidentSource_norm_sq (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    ‖incidentSource k n e D hD hfin‖ ^ 2 = volume.real D * ‖e‖ ^ 2 := by
  rw [← lp_integral_norm_sq volume]
  calc
    _ = ∫ x : Position, D.indicator (fun _ => ‖e‖ ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [incidentSource_coe k n e D hD hfin] with x hx
      rw [hx]
      by_cases hd : x ∈ D <;> simp [hd, incidentWave_norm]
    _ = _ := by rw [integral_indicator hD, integral_const]; simp [Measure.real]

theorem incidentSource_opposite_norm_sq (k : ℝ) (hk : 0 ≤ k) (n : UnitSphere)
    (e : Vector) (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖incidentSource k n e D hD hfin - incidentSource (-k) n e D hD hfin‖ ^ 2 ≤
      4 * k ^ 2 * R ^ 2 * volume.real D * ‖e‖ ^ 2 := by
  let f := incidentSource k n e D hD hfin - incidentSource (-k) n e D hD hfin
  have hb : ∀ᵐ x ∂volume, ‖f x‖ ^ 2 ≤ D.indicator (fun _ => (2 * k * R * ‖e‖) ^ 2) x := by
    filter_upwards [incidentSource_coe k n e D hD hfin,
      incidentSource_coe (-k) n e D hD hfin,
      Lp.coeFn_sub (incidentSource k n e D hD hfin) (incidentSource (-k) n e D hD hfin)] with x hp hm hs
    change ‖(incidentSource k n e D hD hfin - incidentSource (-k) n e D hD hfin) x‖ ^ 2 ≤ _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hp, hm]
    by_cases hd : x ∈ D
    · simp only [indicator_of_mem hd]
      have hx : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hsub hd
      have hh := (incidentWave_opposite_difference k hk n e x).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 * k)) (norm_nonneg e))
      nlinarith [norm_nonneg (incidentWave k n e x - incidentWave (-k) n e x),
        mul_nonneg (show 0 ≤ 2 * k * R by positivity) (norm_nonneg e)]
    · simp [hd]
  have hi : Integrable (D.indicator (fun _ : Position => (2 * k * R * ‖e‖) ^ 2)) volume :=
    (integrable_indicator_iff hD).mpr (integrableOn_const hfin)
  have h := integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg ‖f x‖) hi hb
  rw [lp_integral_norm_sq volume f, integral_indicator hD, integral_const] at h
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at h
  dsimp [f] at h
  dsimp only [Measure.real]
  convert h using 1 <;> ring

end QuarticMaxwell
