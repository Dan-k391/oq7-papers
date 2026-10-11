import PrescribedExtinction.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
namespace OQ7Prescribed

/-- A finite aperture and finite thickness enclose the support in a finite ball. -/
theorem domain_subset_closedBall (B : TwoLayerBody) :
    B.domain ⊆ Metric.closedBall 0
      (B.aperture + B.absorberThickness + B.plateThickness) := by
  intro x hx
  rcases hx with ⟨⟨hx0l, hx0r, hx1l, hx1r⟩, hx2l, hx2r⟩
  have hR := B.aperture_pos
  have hh := B.absorberThickness_pos
  have hd := B.plateThickness_pos
  have h0 : (x 0) ^ 2 ≤ (B.aperture / 2) ^ 2 := by nlinarith
  have h1 : (x 1) ^ 2 ≤ (B.aperture / 2) ^ 2 := by nlinarith
  have h2 : (x 2) ^ 2 ≤ (B.absorberThickness + B.plateThickness) ^ 2 := by
    nlinarith
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  simp [Fin.sum_univ_succ] at hnorm
  have hbound : ‖x‖ ≤ B.aperture + B.absorberThickness + B.plateThickness := by
    nlinarith [norm_nonneg x]
  simpa [Metric.mem_closedBall, dist_zero_right] using hbound

theorem domain_compact_closure (B : TwoLayerBody) : IsCompact (closure B.domain) := by
  apply (isCompact_closedBall (0 : Position)
    (B.aperture + B.absorberThickness + B.plateThickness)).of_isClosed_subset
    isClosed_closure
  exact closure_minimal (domain_subset_closedBall B) Metric.isClosed_closedBall

/-- Vacuum outside the finite slab; no infinite-aperture object is admissible here. -/
theorem permittivity_one_outside (B : TwoLayerBody) (x : Position)
    (hx : x ∉ B.domain) : B.permittivity x = 1 := by
  simp [TwoLayerBody.permittivity, hx]

theorem permittivity_reciprocal (B : TwoLayerBody) (P Q : ℝ)
    (hB : B.admissible P Q) (x : Position) :
    (B.permittivity x).transpose = B.permittivity x := by
  classical
  simp only [TwoLayerBody.permittivity]
  split_ifs
  · exact hB.1.1
  · exact hB.2.1
  · simp

end OQ7Prescribed
