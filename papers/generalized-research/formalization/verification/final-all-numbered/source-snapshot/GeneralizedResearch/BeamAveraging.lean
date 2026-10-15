import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-! Normalized finite-power apertures, narrow-spectrum averaging and exact
target tuning. These analytic results require a separately proved physical
oblique Maxwell fiber family; they do not assume or assert that bridge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GeneralizedResearch
namespace BeamAveraging
open MeasureTheory Set Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α]

def average (μ : Measure α) (K : Set α) (f : α → ℝ) : ℝ :=
  (μ.real K)⁻¹ * ∫ x in K, f x ∂μ

theorem average_const (μ : Measure α) (K : Set α) (hmass : 0 < μ.real K) (c : ℝ) :
    average μ K (fun _ => c) = c := by
  unfold average
  rw [setIntegral_const, smul_eq_mul]
  field_simp

theorem average_sub_const (μ : Measure α) (K : Set α) (hfin : μ K ≠ ⊤)
    (hmass : 0 < μ.real K) (f : α → ℝ) (hf : IntegrableOn f K μ) (c : ℝ) :
    average μ K f - c = average μ K (fun x => f x - c) := by
  unfold average
  rw [integral_sub hf (integrableOn_const hfin), setIntegral_const, smul_eq_mul]
  field_simp

theorem average_error (μ : Measure α) (K : Set α) (hfin : μ K ≠ ⊤)
    (hmass : 0 < μ.real K) (f : α → ℝ) (hf : IntegrableOn f K μ) (c ε : ℝ)
    (hb : ∀ x ∈ K, |f x - c| ≤ ε) : |average μ K f - c| ≤ ε := by
  rw [average_sub_const μ K hfin hmass f hf c]
  unfold average
  rw [abs_mul, abs_of_pos (inv_pos.mpr hmass)]
  have hh := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K)
    (f := fun x => f x - c) (C := ε) hfin.lt_top
    (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx)
  change |∫ x in K, f x - c ∂μ| ≤ ε * μ.real K at hh
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hmass.le)).trans_eq
  field_simp

def aperture (μ : Measure α) (K : Set α) : α → ℝ :=
  K.indicator (fun _ => (Real.sqrt (μ.real K))⁻¹)

theorem aperture_memLp (μ : Measure α) (K : Set α) (hK : MeasurableSet K) (hfin : μ K ≠ ⊤) :
    MemLp (aperture μ K) 2 μ := by
  let : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hfin.lt_top⟩
  rw [aperture, memLp_indicator_iff_restrict hK]
  exact memLp_const _

theorem aperture_unit_power (μ : Measure α) (K : Set α) (hK : MeasurableSet K)
    (hmass : 0 < μ.real K) : (∫ x, aperture μ K x ^ 2 ∂μ) = 1 := by
  have he : (fun x => aperture μ K x ^ 2) = K.indicator (fun _ => ((Real.sqrt (μ.real K))⁻¹) ^ 2) := by
    funext x
    by_cases hx : x ∈ K <;> simp [aperture, hx]
  rw [he, integral_indicator hK, setIntegral_const, smul_eq_mul, inv_pow,
    Real.sq_sqrt hmass.le]
  exact mul_inv_cancel₀ hmass.ne'

theorem aperture_average (μ : Measure α) (K : Set α) (hK : MeasurableSet K)
    (hmass : 0 < μ.real K) (f : α → ℝ) :
    (∫ x, aperture μ K x ^ 2 * f x ∂μ) = average μ K f := by
  have he : (fun x => aperture μ K x ^ 2 * f x) =
      K.indicator (fun x => ((Real.sqrt (μ.real K))⁻¹) ^ 2 * f x) := by
    funext x
    by_cases hx : x ∈ K <;> simp [aperture, hx]
  rw [he, integral_indicator hK, integral_const_mul, inv_pow, Real.sq_sqrt hmass.le]
  rfl

theorem average_continuousOn (μ : Measure α) (K : Set α) (hK : MeasurableSet K)
    (hfin : μ K ≠ ⊤) (F : ℝ → α → ℝ) (J : Set ℝ) (C : ℝ)
    (hm : ∀ t ∈ J, AEStronglyMeasurable (F t) (μ.restrict K))
    (hb : ∀ t ∈ J, ∀ x ∈ K, ‖F t x‖ ≤ C)
    (hc : ∀ x ∈ K, ContinuousOn (fun t => F t x) J) :
    ContinuousOn (fun t => average μ K (F t)) J := by
  have hi : ContinuousOn (fun t => ∫ x in K, F t x ∂μ) J := by
    apply continuousOn_of_dominated hm
    · intro t ht
      filter_upwards [ae_restrict_mem hK] with x hx
      exact hb t ht x hx
    · exact integrableOn_const hfin
    · filter_upwards [ae_restrict_mem hK] with x hx
      exact hc x hx
  exact continuousOn_const.mul hi

theorem exact_target (μ : Measure α) (K : Set α) (X D : ℝ → α → ℝ)
    {a b target value ε : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn (fun t => average μ K (X t)) (Icc a b))
    (hleft : target ≤ average μ K (X a)) (hright : average μ K (X b) ≤ target)
    (hD : ∀ t ∈ Icc a b, value - ε ≤ average μ K (D t)) :
    ∃ t ∈ Icc a b, average μ K (X t) = target ∧ value - ε ≤ average μ K (D t) := by
  obtain ⟨t, ht, hXt⟩ := intermediate_value_Icc' hab hc ⟨hright, hleft⟩
  exact ⟨t, ht, hXt, hD t ht⟩

abbrev Transverse := EuclideanSpace ℝ (Fin 2)

def diskAverage (r : ℝ) (f : Transverse → ℝ) : ℝ :=
  average volume (Metric.closedBall 0 r) f

theorem disk_mass_pos {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure Transverse).real (Metric.closedBall 0 r) :=
  ENNReal.toReal_pos (Metric.measure_closedBall_pos volume (0 : Transverse) hr).ne'
    (isCompact_closedBall (0 : Transverse) r).measure_ne_top

theorem uniformly_narrow {a b R : ℝ} (hR : 0 < R)
    (F : ℝ → Transverse → ℝ)
    (hc : ContinuousOn (fun z : ℝ × Transverse => F z.1 z.2)
      (Icc a b ×ˢ Metric.closedBall 0 R)) :
    ∀ ε > 0, ∃ δ > 0, δ ≤ R ∧ ∀ r, 0 < r → r ≤ δ →
      ∀ t ∈ Icc a b, |diskAverage r (F t) - F t 0| ≤ ε := by
  intro ε hε
  have hu := (isCompact_Icc.prod (isCompact_closedBall (0 : Transverse) R)).uniformContinuousOn_of_continuous hc
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let δ := min R (d / 2)
  have hδ : 0 < δ := lt_min hR (by positivity)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro r hr hrd t ht
  have hrR : r ≤ R := hrd.trans (min_le_left _ _)
  have hslice : ContinuousOn (F t) (Metric.closedBall 0 r) := by
    apply hc.comp (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨ht, Metric.closedBall_subset_closedBall hrR hx⟩
  apply average_error volume (Metric.closedBall (0 : Transverse) r)
    (isCompact_closedBall _ _).measure_ne_top (disk_mass_pos hr) _
    (hslice.integrableOn_compact (isCompact_closedBall _ _)) (F t 0) ε
  intro x hx
  have hxR := Metric.closedBall_subset_closedBall hrR hx
  have hxnorm : ‖x‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hdist : dist (t, x) (t, (0 : Transverse)) < d := by
    simp only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg x)]
    exact hxnorm.trans_lt (lt_of_le_of_lt (hrd.trans (min_le_right _ _)) (by linarith))
  have hh := hclose (t, x) ⟨ht, hxR⟩ (t, (0 : Transverse))
    ⟨ht, Metric.mem_closedBall_self hR.le⟩ hdist
  have hh' : |F t x - F t 0| < ε := by simpa only [Real.dist_eq] using hh
  exact hh'.le

theorem diskAverage_continuousOn {a b R r : ℝ} (hrR : r ≤ R)
    (F : ℝ → Transverse → ℝ)
    (hc : ContinuousOn (fun z : ℝ × Transverse => F z.1 z.2)
      (Icc a b ×ˢ Metric.closedBall 0 R)) :
    ContinuousOn (fun t => diskAverage r (F t)) (Icc a b) := by
  have hsmall : ContinuousOn (fun z : ℝ × Transverse => F z.1 z.2)
      (Icc a b ×ˢ Metric.closedBall 0 r) := hc.mono (prod_mono Subset.rfl (Metric.closedBall_subset_closedBall hrR))
  have hK := isCompact_closedBall (0 : Transverse) r
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).bddAbove_image hsmall.norm
  apply average_continuousOn volume (Metric.closedBall (0 : Transverse) r)
    hK.measurableSet hK.measure_ne_top F (Icc a b) C
  · intro t ht
    have hs : ContinuousOn (F t) (Metric.closedBall 0 r) :=
      hsmall.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨ht, hx⟩)
    exact (hs.integrableOn_compact hK).aestronglyMeasurable
  · intro t ht x hx
    apply hC
    exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  · intro x hx
    exact hsmall.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, hx⟩)

/-- A narrow, unit-power spectral aperture attains exactly the prescribed
extinction. Bracketing and the signed difference are proved after averaging. -/
theorem narrow_exact_target {a b t0 R ε value : ℝ} (ha : a < t0) (hb : t0 < b)
    (hR : 0 < R) (hε : 0 < ε) (X D : ℝ → Transverse → ℝ)
    (hX : ContinuousOn (fun z : ℝ × Transverse => X z.1 z.2) (Icc a b ×ˢ Metric.closedBall 0 R))
    (hD : ContinuousOn (fun z : ℝ × Transverse => D z.1 z.2) (Icc a b ×ˢ Metric.closedBall 0 R))
    (hnormal : ∀ t ∈ Icc a b, X t 0 = 2 * (1 - t))
    (hvalue : ∀ t ∈ Icc a b, value - ε / 2 ≤ D t 0) :
    ∃ r, 0 < r ∧ r ≤ R ∧ ∃ t ∈ Icc a b,
      diskAverage r (X t) = 2 * (1 - t0) ∧ value - ε ≤ diskAverage r (D t) := by
  let margin := min (t0 - a) (b - t0)
  have hm : 0 < margin := lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)
  obtain ⟨δX, hδX, hδXR, hXclose⟩ := uniformly_narrow hR X hX margin hm
  obtain ⟨δD, hδD, hδDR, hDclose⟩ := uniformly_narrow hR D hD (ε / 2) (by positivity)
  let r := min δX δD
  have hr : 0 < r := lt_min hδX hδD
  have hrX : r ≤ δX := min_le_left _ _
  have hrD : r ≤ δD := min_le_right _ _
  have hrR : r ≤ R := hrX.trans hδXR
  have hab : a ≤ b := (ha.trans hb).le
  have hleft : 2 * (1 - t0) ≤ diskAverage r (X a) := by
    have hh := hXclose r hr hrX a (left_mem_Icc.mpr hab)
    rw [hnormal a (left_mem_Icc.mpr hab)] at hh
    have hh' := (abs_le.mp hh).1
    have hmleft : margin ≤ t0 - a := min_le_left _ _
    linarith
  have hright : diskAverage r (X b) ≤ 2 * (1 - t0) := by
    have hh := hXclose r hr hrX b (right_mem_Icc.mpr hab)
    rw [hnormal b (right_mem_Icc.mpr hab)] at hh
    have hh' := (abs_le.mp hh).2
    have hmright : margin ≤ b - t0 := min_le_right _ _
    linarith
  obtain ⟨t, ht, htarget⟩ := intermediate_value_Icc' hab (diskAverage_continuousOn hrR X hX) ⟨hright, hleft⟩
  have hd := hDclose r hr hrD t ht
  have hd' := (abs_le.mp hd).1
  exact ⟨r, hr, hrR, t, ht, htarget, by linarith [hvalue t ht]⟩

end BeamAveraging
end GeneralizedResearch
