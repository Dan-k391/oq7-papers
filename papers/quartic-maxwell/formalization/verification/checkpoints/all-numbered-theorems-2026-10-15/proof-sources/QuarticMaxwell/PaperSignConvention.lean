import QuarticMaxwell.HeterogeneousRemainder

/-! Literal exp(+ik n.x) incident labels used in the manuscript. The analytic
library uses exp(-ik n.x); swapping the two physical incident labels reverses
signed scattering and leaves the absorption contrast unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.PaperSignConvention
open OQ7Prescribed MeasureTheory WeakMaterial PhysicalPowers FixedPatternWork
open FixedPatternScattering FixedPatternContrast

theorem incidentWave_plus (k : ℝ) (n : UnitSphere) (e : Vector) (x : Position) :
    incidentWave k (opposite n) e x =
      Complex.exp (Complex.I * ((k * inner ℝ (n : Position) x : ℝ) : ℂ)) • e := by
  rw [incidentWave_opposite]
  unfold incidentWave radiationPhase
  congr 2
  push_cast
  ring

def signedScatteringPaper (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) : ℝ :=
  -signedScattering B t ht n e

def leadingPaper (B : Medium) (n : UnitSphere) (e : Vector) : ℝ := -leading B n e

theorem leadingPaper_moment (B : Medium) (n : UnitSphere) (e : Vector) :
    leadingPaper B n e = -(2 / (3 * Real.pi)) *
      (inner ℂ (moment0 B e) (moment1 B n e)).im := by
  unfold leadingPaper leading
  ring

theorem actual_scattering_difference (B : Medium) (t : ℝ) (ht : 0 < t)
    (n : UnitSphere) (e : Vector) (htr : bilinear (complexify (n : Position)) e = 0)
    (plus : State B t (opposite n) e) (minus : State B t n e) :
    scattering B t plus.electric plus.electric_L2 - scattering B t minus.electric minus.electric_L2 =
      t ^ 4 * signedScatteringPaper B t ht n e := by
  have h := state_scattering_difference B t ht n e htr minus plus
  unfold signedScatteringPaper
  linarith

def contrastPaper (B : Medium) (t : ℝ) (n : UnitSphere) (e : Vector)
    (plus : State B t (opposite n) e) (minus : State B t n e) : ℝ :=
  |absorption B t plus.electric - absorption B t minus.electric| /
    extinction B t (opposite n) e plus.electric

theorem contrastPaper_eq (B : Medium) (t : ℝ) (ht : 0 < t)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ a b : Vector,
      bilinear a (B.susceptibility x b) = bilinear b (B.susceptibility x a))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (plus : State B t (opposite n) e) (minus : State B t n e) :
    contrastPaper B t n e plus minus = contrast B t n e minus plus := by
  unfold contrastPaper contrast
  rw [abs_sub_comm, ← state_extinction_reciprocal B ht hsym n e he htr minus plus]

theorem signed_error (B : Medium) (hV : 0 < volume.real B.domain)
    (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) :
    |signedScatteringPaper B t ht n e - t * leadingPaper B n e| ≤ errorConstant B e * t ^ 3 := by
  have h := signedScattering_error B hV t ht n e
  have heq : signedScatteringPaper B t ht n e - t * leadingPaper B n e =
      -(signedScattering B t ht n e - leading B n e * t) := by unfold signedScatteringPaper leadingPaper; ring
  rw [heq, abs_neg]
  exact h

theorem heterogeneous_signed_error (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1)
    (t : ℝ) (ht : 0 < t) :
    |signedScatteringPaper (HeterogeneousRemainder.body n) t ht n e -
      t * leadingPaper (HeterogeneousRemainder.body n) n e| ≤
      168 / (25 * Real.pi) * HeterogeneousRemainder.w n ^ 2 * t ^ 3 := by
  have h := (HeterogeneousRemainder.physical_errors n e hen t ht).1
  have heq : signedScatteringPaper (HeterogeneousRemainder.body n) t ht n e -
      t * leadingPaper (HeterogeneousRemainder.body n) n e =
      -(signedScattering (HeterogeneousRemainder.body n) t ht n e -
        t * leading (HeterogeneousRemainder.body n) n e) := by unfold signedScatteringPaper leadingPaper; ring
  rw [heq, abs_neg]
  exact h

theorem coefficient_paper (B : Medium) (n : UnitSphere) (e : Vector) :
    coefficient B n e = |leadingPaper B n e| / D0 B e := by simp [coefficient, leadingPaper]

end QuarticMaxwell.PaperSignConvention
