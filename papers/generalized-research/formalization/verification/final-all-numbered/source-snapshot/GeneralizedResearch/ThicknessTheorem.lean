import OQ7.SharpPhysicalConstruction
import OQ7.PhysicalGlobal

/-! # Exact original Theorem 5.1 correspondence

This wrapper exposes the literal finite-layer optimization statement from the
already audited scalar Maxwell development. The imported library is preserved
byte-for-byte; the statement is not a replacement algebraic model and has no
assumed matching-sequence or material-floor hypotheses. -/

noncomputable section
namespace GeneralizedResearch
open Filter
open scoped Topology

/-- Original Theorem 5.1, also the arXiv revision's `thm:thickness`:
eventual exact targets, a strict finite-stack gap and the sharp supremum limit. -/
theorem sharp_exact_target_thickness (p : OQ7.PhysicalParameters) :
    (∀ᶠ L : ℝ in atTop, (OQ7.exactTargetClass p L).Nonempty) ∧
    (∀ (L : ℝ) (layers : List OQ7.HomogeneousLayer),
      layers ∈ OQ7.exactTargetClass p L →
        OQ7.stackAsymmetry p.k layers < OQ7.ScalarEnvelope.D0 p.T p.a) ∧
    Tendsto
      (fun L : ℝ => (p.k * L) ^ 2 *
        (OQ7.ScalarEnvelope.D0 p.T p.a - OQ7.optimalAsymmetry p L))
      atTop (𝓝 (OQ7.ScalarEnvelope.alpha p.T p.a * Real.pi ^ 2 *
        (p.k * p.M) ^ 4 / (3 * p.P * p.Q ^ 2))) :=
  OQ7.theorem51 p

/-- Every homogeneous layer in the exact-target class has a literal electric
field solving the scalar Helmholtz equation, rather than only a transfer label. -/
theorem admissible_layer_helmholtz (p : OQ7.PhysicalParameters) (L : ℝ)
    (layers : List OQ7.HomogeneousLayer) (h : layers ∈ OQ7.exactTargetClass p L)
    (layer : OQ7.HomogeneousLayer) (hlayer : layer ∈ layers)
    (E₀ H₀ : ℂ) (z : ℝ) :
    deriv (deriv (OQ7.layerElectricField p.k layer E₀ H₀)) z +
      (p.k : ℂ) ^ 2 * OQ7.relativePermittivity layer *
        OQ7.layerElectricField p.k layer E₀ H₀ z = 0 := by
  exact OQ7.layerElectricField_helmholtz p.k (h.1 layer hlayer).1 E₀ H₀ z

/-- Continuity of the actual field state includes all layer interfaces. -/
theorem exact_target_field_continuous (p : OQ7.PhysicalParameters) (L : ℝ)
    (layers : List OQ7.HomogeneousLayer) (h : layers ∈ OQ7.exactTargetClass p L)
    (v : Fin 2 → ℂ) : Continuous (OQ7.partialState p.k layers v) :=
  OQ7.partialState_continuous p.k h.1 v

#print axioms sharp_exact_target_thickness
#print axioms admissible_layer_helmholtz
#print axioms exact_target_field_continuous

end GeneralizedResearch
