import PrescribedExtinction.DyadicRemainder
import PrescribedExtinction.VolumePotential
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Local L² integrability and actual convolution of the proved classical
dynamic-minus-static remainder. No identification with a distributional
derivative or Maxwell scattering state is assumed. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Convolution ENNReal

-- Fix the canonical Mathlib instances before forming the curried evaluation map.
local instance : NormedAddCommGroup (Vector →L[ℂ] Vector) := inferInstance
local instance : NormedSpace ℂ (Vector →L[ℂ] Vector) := inferInstance
local instance : NormedAddCommGroup ((Vector →L[ℂ] Vector) →L[ℂ] Vector) := inferInstance
local instance : NormedSpace ℂ ((Vector →L[ℂ] Vector) →L[ℂ] Vector) := inferInstance

def cutoffDyadicRemainder (k T : ℝ) : Position → Vector →L[ℂ] Vector :=
  (Metric.closedBall 0 T).indicator (dyadicRemainder k)

def dyadicRemainderCutoffConstant (k T : ℝ) : ℝ :=
  k ^ 2 * greenCancellationEnvelope (|k| * |T|)

theorem cutoffDyadicRemainder_norm_le (k T : ℝ) (x : Position) :
    ‖cutoffDyadicRemainder k T x‖ ≤
      dyadicRemainderCutoffConstant k T * ‖cutoffGreen 0 T x‖ := by
  classical
  by_cases hx : x ∈ Metric.closedBall 0 T
  · have hn : ‖x‖ ≤ |T| := by
      have h := Metric.mem_closedBall.mp hx
      simpa only [dist_zero_right] using h.trans (le_abs_self T)
    have h := dyadicRemainder_norm_le_on_ball k |T| x hn
    simpa [cutoffDyadicRemainder, cutoffGreen, hx, outgoingGreen_norm,
      dyadicRemainderCutoffConstant, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm] using h
  · simp [cutoffDyadicRemainder, cutoffGreen, hx]

theorem cutoffDyadicRemainder_memLp (k T : ℝ) :
    MemLp (cutoffDyadicRemainder k T) 2 volume := by
  have hm : AEStronglyMeasurable (cutoffDyadicRemainder k T) volume :=
    ((dyadicRemainder_measurable k).indicator
      Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable
  exact (cutoffGreen_memLp 0 T).of_le_mul hm
    (ae_of_all _ fun x => cutoffDyadicRemainder_norm_le k T x)

theorem cutoffDyadicRemainder_eLpNorm_le (k T : ℝ) :
    eLpNorm (cutoffDyadicRemainder k T) 2 volume ≤
      ENNReal.ofReal (dyadicRemainderCutoffConstant k T) * eLpNorm (cutoffGreen 0 T) 2 volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (cutoffDyadicRemainder_memLp k T).aestronglyMeasurable
    (ae_of_all _ fun x => cutoffDyadicRemainder_norm_le k T x)

def vectorOperatorApply : Vector →L[ℂ] (Vector →L[ℂ] Vector) →L[ℂ] Vector :=
  ContinuousLinearMap.apply ℂ Vector

def remainderPotential (k : ℝ) (p : CompactPolarization) : Field :=
  p.current ⋆[vectorOperatorApply, volume] dyadicRemainder k

theorem remainderPotential_integrand_cutoff (k : ℝ) (p : CompactPolarization)
    (S : ℝ) (x y : Position) (hx : ‖x‖ ≤ S) :
    dyadicRemainder k (x - y) (p.current y) =
      cutoffDyadicRemainder k (S + p.radius) (x - y) (p.current y) := by
  classical
  by_cases hy : ‖y‖ ≤ p.radius
  · have hxy : x - y ∈ Metric.closedBall 0 (S + p.radius) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact (norm_sub_le x y).trans (add_le_add hx hy)
    simp [cutoffDyadicRemainder, hxy]
  · simp [p.vanish y (lt_of_not_ge hy)]

theorem remainderPotential_integrable (k : ℝ) (p : CompactPolarization) (x : Position) :
    Integrable (fun y => dyadicRemainder k (x - y) (p.current y)) volume := by
  have h := ConvolutionExists.of_memLp_memLp (L := vectorOperatorApply)
    p.memLp (cutoffDyadicRemainder_memLp k (‖x‖ + p.radius)) x
  exact h.congr (ae_of_all _ fun y =>
    (remainderPotential_integrand_cutoff k p ‖x‖ x y le_rfl).symm)

def remainderPotentialBound (k : ℝ) (p : CompactPolarization) (S : ℝ) : ℝ≥0∞ :=
  ‖vectorOperatorApply‖ₑ * eLpNorm p.current 2 volume *
    eLpNorm (cutoffDyadicRemainder k (S + p.radius)) 2 volume

theorem remainderPotentialBound_lt_top (k : ℝ) (p : CompactPolarization) (S : ℝ) :
    remainderPotentialBound k p S < ⊤ := by
  unfold remainderPotentialBound
  finiteness [p.memLp.eLpNorm_lt_top,
    (cutoffDyadicRemainder_memLp k (S + p.radius)).eLpNorm_lt_top]

theorem remainderPotential_enorm_le (k : ℝ) (p : CompactPolarization)
    (S : ℝ) (x : Position) (hx : ‖x‖ ≤ S) :
    ‖remainderPotential k p x‖ₑ ≤ remainderPotentialBound k p S := by
  have he : remainderPotential k p x =
      (p.current ⋆[vectorOperatorApply, volume] cutoffDyadicRemainder k (S + p.radius)) x :=
    integral_congr_ae (ae_of_all _ fun y => remainderPotential_integrand_cutoff k p S x y hx)
  rw [he]
  exact enorm_convolution_le (L := vectorOperatorApply) (p := 2) (q := 2) p.memLp.aestronglyMeasurable
    (cutoffDyadicRemainder_memLp k (S + p.radius)).aestronglyMeasurable x

theorem remainderPotential_aestronglyMeasurable (k : ℝ) (p : CompactPolarization) :
    AEStronglyMeasurable (remainderPotential k p) volume :=
  p.memLp.aestronglyMeasurable.convolution (L := vectorOperatorApply)
    (dyadicRemainder_measurable k).aestronglyMeasurable

theorem remainderPotential_memLp_on_compact (k : ℝ) (p : CompactPolarization)
    (K : Set Position) (hK : IsCompact K) :
    MemLp (remainderPotential k p) 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨S, hS, hKS⟩ := hK.isBounded.exists_pos_norm_lt
  apply MemLp.of_bound ((remainderPotential_aestronglyMeasurable k p).restrict)
    (remainderPotentialBound k p S).toReal
  apply ae_restrict_of_forall_mem hK.measurableSet
  intro x hx
  exact ENNReal.toReal_mono (remainderPotentialBound_lt_top k p S).ne
    (remainderPotential_enorm_le k p S x (hKS x hx).le)

theorem remainderPotential_congr_current (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : remainderPotential k p = remainderPotential k q := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem remainderPotential_add (k : ℝ) (p q : CompactPolarization) :
    remainderPotential k (p.add q) = remainderPotential k p + remainderPotential k q := by
  funext x
  change (∫ y : Position, dyadicRemainder k (x - y) (p.current y + q.current y)) =
    (∫ y : Position, dyadicRemainder k (x - y) (p.current y)) +
      (∫ y : Position, dyadicRemainder k (x - y) (q.current y))
  simp_rw [map_add]
  exact integral_add (remainderPotential_integrable k p x) (remainderPotential_integrable k q x)

def CompactPolarization.scale (z : ℂ) (p : CompactPolarization) : CompactPolarization where
  current := z • p.current
  radius := p.radius
  radius_nonneg := p.radius_nonneg
  memLp := p.memLp.const_smul z
  vanish x hx := by simp [p.vanish x hx]

theorem remainderPotential_smul (k : ℝ) (z : ℂ) (p : CompactPolarization) :
    remainderPotential k (p.scale z) = z • remainderPotential k p := by
  funext x
  change (∫ y : Position, dyadicRemainder k (x - y) (z • p.current y)) =
    z • (∫ y : Position, dyadicRemainder k (x - y) (p.current y))
  simp_rw [map_smul]
  exact integral_smul z _

theorem remainderPotential_eLpNorm_le (k : ℝ) (p : CompactPolarization)
    (K : Set Position) (hK : MeasurableSet K) (S : ℝ)
    (hKS : ∀ x ∈ K, ‖x‖ ≤ S) :
    eLpNorm (remainderPotential k p) 2 (volume.restrict K) ≤
      remainderPotentialBound k p S * volume K ^ (1 / (2 : ℝ)) := by
  have h := eLpNorm_le_of_ae_enorm_bound (p := 2)
    ((remainderPotential_aestronglyMeasurable k p).restrict)
    (ae_restrict_of_forall_mem hK fun x hx => remainderPotential_enorm_le k p S x (hKS x hx))
  simpa using h

end OQ7Prescribed
