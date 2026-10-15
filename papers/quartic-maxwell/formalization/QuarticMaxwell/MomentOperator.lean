import QuarticMaxwell.RadiationGram
import QuarticMaxwell.RadiationTaylor

/-! The actual support-integration map as a bounded complex-linear map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.MomentOperator
open MeasureTheory Set OQ7Prescribed

theorem norm_le (D : Set Position) (hfin : volume D ≠ ⊤) (p : DomainL2 D) :
    ‖supportMomentLinear D hfin p‖ ≤ Real.sqrt (volume.real D) * ‖p‖ := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin.lt_top⟩
  have h := norm_integral_sq_le_measure_mul_square (volume.restrict D) (fun x => (p : VectorL2) x)
    ((Lp.memLp (p : VectorL2)).restrict D)
  have hi : Integrable (fun x => ‖(p : VectorL2) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (p : VectorL2))).mp (Lp.memLp (p : VectorL2))
  have hsource : (∫ x in D, ‖(p : VectorL2) x‖ ^ 2) ≤ ‖p‖ ^ 2 := by
    change _ ≤ ‖(p : VectorL2)‖ ^ 2
    rw [← lp_integral_norm_sq volume]
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => sq_nonneg _) hi
  have hs : ‖supportMomentLinear D hfin p‖ ^ 2 ≤ volume.real D * ‖p‖ ^ 2 := by
    apply h.trans
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      mul_le_mul_of_nonneg_left hsource (show 0 ≤ volume.real D by positivity)
  have hn := nonnegative_norm_of_square_bound (norm_nonneg _) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ volume.real D)
    (by simpa only [one_pow, one_mul] using hs)
  simpa only [mul_one] using hn

def map (D : Set Position) (hfin : volume D ≠ ⊤) : DomainL2 D →L[ℂ] Vector :=
  (supportMomentLinear D hfin).mkContinuous (Real.sqrt (volume.real D)) (norm_le D hfin)

theorem map_norm_le (D : Set Position) (hfin : volume D ≠ ⊤) : ‖map D hfin‖ ≤ Real.sqrt (volume.real D) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

theorem map_apply (D : Set Position) (hfin : volume D ≠ ⊤) (p : DomainL2 D) :
    map D hfin p = ∫ x in D, (p : VectorL2) x := rfl

theorem full_integral (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) (p : DomainL2 D) :
    map D hfin p = ∫ x, (p : VectorL2) x := by
  rw [map_apply, ← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [p.property] with x hx
  by_cases hxs : x ∈ D
  · simp only [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs, hx hxs]

theorem response_difference_norm_le (D : Set Position) (hfin : volume D ≠ ⊤)
    (T A : DomainL2 D →L[ℂ] DomainL2 D) {δ : ℝ} (hδ : ‖T - A‖ ≤ δ) (f : DomainL2 D) :
    ‖map D hfin (T f) - map D hfin (A f)‖ ≤ Real.sqrt (volume.real D) * δ * ‖f‖ := by
  rw [← (map D hfin).map_sub]
  apply (norm_le D hfin (T f - A f)).trans
  have hn := ((T - A).le_opNorm f).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg f))
  simpa only [sub_apply, mul_assoc] using mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (volume.real D))

end QuarticMaxwell.MomentOperator
