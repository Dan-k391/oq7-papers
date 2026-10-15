import GeneralizedResearch.ScalarPhaseFeasibility

/-! Exact phase twisting and port interchange of actual passive two-ports. -/
noncomputable section
namespace GeneralizedResearch.ScalarPhaseSymmetry
open OQ7 ScalarBenchmark ScalarPhaseFeasibility

theorem phase_twist_interference (rL rR t u : ℂ) :
    interference (u * rL) (star u * rR) t = star u * interference rL rR t := by
  simp only [interference, star_mul]
  ring

theorem phase_twist_observables (rL rR t u : ℂ) (hu : ‖u‖ = 1) :
    meanAbsorptance (u * rL) (star u * rR) t = meanAbsorptance rL rR t ∧
    halfAsymmetry (u * rL) (star u * rR) t = halfAsymmetry rL rR t ∧
    Complex.normSq (interference (u * rL) (star u * rR) t) =
      Complex.normSq (interference rL rR t) := by
  have hs : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hss : Complex.normSq (star u) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_star, hu]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp only [meanAbsorptance, absorptanceLeft, absorptanceRight, Complex.normSq_mul, hs, hss, one_mul]
  · simp only [halfAsymmetry, absorptanceLeft, absorptanceRight, Complex.normSq_mul, hs, hss, one_mul]
  · rw [phase_twist_interference, Complex.normSq_mul, hss, one_mul]

theorem phase_twist_passive (rL rR t u : ℂ) (hu : ‖u‖ = 1) :
    Passive (u * rL) (star u * rR) t ↔ Passive rL rR t := by
  obtain ⟨ha, hd, hz⟩ := phase_twist_observables rL rR t u hu
  rw [passive_iff_magnitudes_det, passive_iff_magnitudes_det]
  simp only [MagnitudeConditions, ha, hd, hz]

theorem swap_interference (rL rR t : ℂ) :
    interference rR rL t = star (interference rL rR t) := by
  simp only [interference, star_add, star_mul, star_star]
  ring

theorem swap_observables (rL rR t : ℂ) :
    meanAbsorptance rR rL t = meanAbsorptance rL rR t ∧
    halfAsymmetry rR rL t = -halfAsymmetry rL rR t ∧
    Complex.normSq (interference rR rL t) = Complex.normSq (interference rL rR t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold meanAbsorptance absorptanceLeft absorptanceRight
    ring
  · unfold halfAsymmetry absorptanceLeft absorptanceRight
    ring
  · rw [swap_interference]
    exact Complex.normSq_conj _

theorem swap_passive (rL rR t : ℂ) : Passive rR rL t ↔ Passive rL rR t := by
  obtain ⟨ha, hd, hz⟩ := swap_observables rL rR t
  rw [passive_iff_magnitudes_det, passive_iff_magnitudes_det]
  simp only [MagnitudeConditions, ha, hd, hz, abs_neg]

end GeneralizedResearch.ScalarPhaseSymmetry
