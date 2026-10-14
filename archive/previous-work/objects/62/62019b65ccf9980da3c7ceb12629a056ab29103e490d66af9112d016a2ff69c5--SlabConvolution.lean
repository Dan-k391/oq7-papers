import work.SlabAngular

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def horizontalSlabPotential (k s : ℝ) (w : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ y : ℂ, slabGreen k s y * w (x - y)

theorem horizontalSlabPotential_integrable (k s : ℝ) (w : ℂ → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (x : ℂ) :
    Integrable (fun y => slabGreen k s y * w (x - y)) volume := by
  have hg : Continuous (fun y : ℂ => w (x - y)) := hw.comp (continuous_const.sub continuous_id)
  have hgc : HasCompactSupport (fun y : ℂ => w (x - y)) := by
    convert hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addLeft x)) using 1
    funext y
    simp [sub_eq_add_neg]
  simpa only [smul_eq_mul] using
    (slabGreen_locallyIntegrable k s).integrable_smul_right_of_hasCompactSupport hg hgc

theorem horizontalSlabPotential_polar (k s : ℝ) (w : ℂ → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (x : ℂ) :
    horizontalSlabPotential k s w x = ∫ r in Ioi (0 : ℝ),
      (2 * Real.pi) • ((r : ℂ) * slabGreen k s (circleMap 0 r 0) * apertureCircleJet 0 w x r) := by
  let f : ℂ → ℂ := fun y => slabGreen k s y * w (x - y)
  have hm : Measurable f := (slabGreen_measurable k s).mul
    (hw.comp (continuous_const.sub continuous_id)).measurable
  have hi := horizontalSlabPotential_integrable k s w hw hc x
  have hpi := slabPolar_integrable f hm hi
  have he := Complex.integral_comp_polarCoord_symm f
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • f (Complex.polarCoord.symm p)) = horizontalSlabPotential k s w x at he
  rw [Measure.volume_eq_prod] at hpi
  rw [← he, Measure.volume_eq_prod, setIntegral_prod _ hpi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [f, slabPolar_symm]
  have hrad (θ : ℝ) : slabGreen k s (circleMap 0 r θ) = slabGreen k s (circleMap 0 r 0) := by
    rw [slabGreen_radial, slabGreen_radial]
  simp_rw [hrad, Complex.real_smul, mul_assoc]
  rw [integral_const_mul, integral_const_mul, slabWindow_circle]
  simp only [Complex.real_smul]
  ring

theorem horizontalSlabPotential_radialWindow (k s : ℝ) (w : ℂ → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (x : ℂ) (U A : ℝ)
    (hU : 0 < U) (hA : tsupport w ⊆ Metric.closedBall 0 A) (hUA : A + ‖x‖ < U) :
    horizontalSlabPotential k s w x = slabRadialWindow k s w x U := by
  rw [horizontalSlabPotential_polar k s w hw hc x]
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (μ := volume)
    (f := fun r : ℝ => (2 * Real.pi) •
      ((r : ℂ) * slabGreen k s (circleMap 0 r 0) * apertureCircleJet 0 w x r))
    measurableSet_Ioi (show Ioc (0 : ℝ) U ⊆ Ioi 0 from fun r hr => hr.1)
    (fun r hr => by
      have hrU : U < r := lt_of_not_ge (fun h => hr.2 ⟨hr.1, h⟩)
      rw [apertureCircleJet_outside_support 0 w x r A hA (hUA.trans hrU)]
      simp)
  rw [he, ← intervalIntegral.integral_of_le hU.le, intervalIntegral.integral_smul]
  rfl

theorem horizontalSlabPotential_error (k : ℝ) (hk : 0 < k) (s : ℝ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (U A C₂ C₄ : ℝ)
    (hU : 0 < U) (hA : tsupport w ⊆ Metric.closedBall 0 A) (hUA : A + ‖x‖ < U)
    (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄) :
    ‖horizontalSlabPotential k s w x - planarScalarGreen k s * w x‖ ≤
      (|s| * C₂ + (C₂ + (slabHeightRadius s U) ^ 2 * C₄ / 3) *
        (slabHeightRadius s U - |s|)) / (2 * k ^ 2) := by
  rw [horizontalSlabPotential_radialWindow k s w hw.continuous hc x U A hU hA hUA]
  exact slabRadialWindow_error k hk s w hw hc x U A C₂ C₄ hU hA hUA h₂ h₄

end OQ7Prescribed
