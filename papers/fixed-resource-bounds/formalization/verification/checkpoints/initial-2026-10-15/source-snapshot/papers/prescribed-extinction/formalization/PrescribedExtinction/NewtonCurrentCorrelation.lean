import PrescribedExtinction.NewtonCurrentPairing
import PrescribedExtinction.NewtonSchwartz
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Genuine compact smooth test correlations for actual compact L² currents.
Smoothness and differentiation follow from Mathlib's convolution theorem,
with the necessary integrability supplied by the current hypotheses. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Convolution ENNReal

def reflectedCurrentComponent (p : CompactPolarization) (j : Fin 3) (y : Position) : ℂ :=
  p.current (-y) j

theorem reflectedCurrentComponent_integrable (p : CompactPolarization) (j : Fin 3) :
    Integrable (reflectedCurrentComponent p j) volume :=
  (current_component_integrable p j).comp_neg

theorem reflectedCurrentComponent_hasCompactSupport (p : CompactPolarization) (j : Fin 3) :
    HasCompactSupport (reflectedCurrentComponent p j) := by
  refine exists_compact_iff_hasCompactSupport.mp
    ⟨Metric.closedBall (0 : Position) p.radius, isCompact_closedBall _ _, ?_⟩
  intro y hy
  have hn : p.radius < ‖y‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  simp only [reflectedCurrentComponent, p.vanish (-y) (by simpa using hn), PiLp.zero_apply]

theorem scalarTestSchwartz_hasCompactSupport (φ : ScalarTest) :
    HasCompactSupport (scalarTestSchwartz φ : Position → ℂ) := by
  change HasCompactSupport (Complex.ofRealCLM ∘ (φ : Position → ℝ))
  exact φ.hasCompactSupport.comp_left rfl

theorem newtonCurrentCorrelation_eq_convolution (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) :
    newtonCurrentCorrelation p φ j =
      reflectedCurrentComponent p j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (scalarTestSchwartz φ : Position → ℂ) := by
  funext z
  change (∫ y : Position, p.current y j * (φ (z + y) : ℂ)) =
    ∫ y : Position, p.current (-y) j * (φ (z - y) : ℂ)
  rw [← integral_neg_eq_self
    (fun y : Position => p.current y j * (φ (z + y) : ℂ)) volume]
  simp only [sub_eq_add_neg]

theorem newtonCurrentCorrelation_hasCompactSupport (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) : HasCompactSupport (newtonCurrentCorrelation p φ j) := by
  rw [newtonCurrentCorrelation_eq_convolution]
  exact (reflectedCurrentComponent_hasCompactSupport p j).convolution
    (ContinuousLinearMap.mul ℝ ℂ) (scalarTestSchwartz_hasCompactSupport φ)

theorem newtonCurrentCorrelation_contDiff (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (newtonCurrentCorrelation p φ j) := by
  rw [newtonCurrentCorrelation_eq_convolution]
  exact (scalarTestSchwartz_hasCompactSupport φ).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) (reflectedCurrentComponent_integrable p j).locallyIntegrable
    ((scalarTestSchwartz φ).smooth ⊤)

theorem scalarTestSchwartz_fderiv_basis (φ : ScalarTest) (i : Fin 3) (x : Position) :
    fderiv ℝ (scalarTestSchwartz φ : Position → ℂ) x (basisR i) =
      ((testPartial i φ) x : ℂ) := by
  have h := congrArg (fun f : SchwartzMap Position ℂ => f x) (scalarTestSchwartz_partial φ i)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, scalarTestSchwartz_apply] at h
  exact h

theorem newtonCurrentCorrelation_hasLineDerivAt (p : CompactPolarization)
    (φ : ScalarTest) (j i : Fin 3) (z : Position) :
    HasLineDerivAt ℝ (newtonCurrentCorrelation p φ j)
      (newtonCurrentCorrelation p (testPartial i φ) j z) z (basisR i) := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hf := (reflectedCurrentComponent_integrable p j).locallyIntegrable
  have hg := scalarTestSchwartz_hasCompactSupport φ
  have hgc : ContDiff ℝ 1 (scalarTestSchwartz φ : Position → ℂ) :=
    (scalarTestSchwartz φ).smooth 1
  have h := (hg.hasFDerivAt_convolution_right L hf hgc z).hasLineDerivAt (basisR i)
  rw [← newtonCurrentCorrelation_eq_convolution p φ j] at h
  have hd : ((reflectedCurrentComponent p j ⋆[L.precompR Position, volume]
      fderiv ℝ (scalarTestSchwartz φ : Position → ℂ)) z) (basisR i) =
      newtonCurrentCorrelation p (testPartial i φ) j z := by
    change (∫ y : Position, L.precompR Position (reflectedCurrentComponent p j y)
      (fderiv ℝ (scalarTestSchwartz φ : Position → ℂ) (z - y))) (basisR i) = _
    rw [ContinuousLinearMap.integral_apply
      ((hg.fderiv ℝ).convolutionExists_right (L.precompR Position) hf
        (hgc.continuous_fderiv one_ne_zero) z)]
    rw [newtonCurrentCorrelation_eq_convolution p (testPartial i φ) j]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change reflectedCurrentComponent p j y *
        (fderiv ℝ (scalarTestSchwartz φ : Position → ℂ) (z - y) (basisR i)) =
        reflectedCurrentComponent p j y * (scalarTestSchwartz (testPartial i φ) (z - y))
      rw [scalarTestSchwartz_fderiv_basis, scalarTestSchwartz_apply]
  rw [hd] at h
  exact h

theorem newtonCurrentCorrelation_lineDeriv (p : CompactPolarization)
    (φ : ScalarTest) (j i : Fin 3) (z : Position) :
    lineDeriv ℝ (newtonCurrentCorrelation p φ j) z (basisR i) =
      newtonCurrentCorrelation p (testPartial i φ) j z :=
  (newtonCurrentCorrelation_hasLineDerivAt p φ j i z).lineDeriv

def newtonCurrentCorrelationSchwartz (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) : SchwartzMap Position ℂ :=
  (newtonCurrentCorrelation_hasCompactSupport p φ j).toSchwartzMap
    (newtonCurrentCorrelation_contDiff p φ j)

theorem newtonCurrentCorrelationSchwartz_apply (p : CompactPolarization)
    (φ : ScalarTest) (j : Fin 3) (z : Position) :
    newtonCurrentCorrelationSchwartz p φ j z = newtonCurrentCorrelation p φ j z := rfl

theorem newtonCurrentCorrelationSchwartz_partial (p : CompactPolarization)
    (φ : ScalarTest) (j i : Fin 3) :
    LineDeriv.lineDerivOp (basisR i) (newtonCurrentCorrelationSchwartz p φ j) =
      newtonCurrentCorrelationSchwartz p (testPartial i φ) j := by
  ext z
  rw [SchwartzMap.lineDerivOp_apply, newtonCurrentCorrelationSchwartz_apply]
  change lineDeriv ℝ (newtonCurrentCorrelation p φ j) z (basisR i) = _
  exact newtonCurrentCorrelation_lineDeriv p φ j i z

theorem newtonCurrentCorrelationSchwartz_secondPartial (p : CompactPolarization)
    (φ : ScalarTest) (l i j : Fin 3) :
    LineDeriv.lineDerivOp (basisR j)
      (LineDeriv.lineDerivOp (basisR i) (newtonCurrentCorrelationSchwartz p φ l)) =
      newtonCurrentCorrelationSchwartz p (testPartial j (testPartial i φ)) l := by
  rw [newtonCurrentCorrelationSchwartz_partial, newtonCurrentCorrelationSchwartz_partial]

end OQ7Prescribed
