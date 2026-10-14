import PrescribedExtinction.GreenKernel
import PrescribedExtinction.Geometry
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Convolution by the actual scalar outgoing kernel on compactly supported
vector L² currents. Compact support and L² membership specify the input class;
no Maxwell, passivity, or inverse identity is assumed of the input. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Convolution Distributions ENNReal

structure CompactPolarization where
  current : Field
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  memLp : MemLp current 2 volume
  vanish : ∀ x : Position, radius < ‖x‖ → current x = 0

def CompactPolarization.add (p q : CompactPolarization) : CompactPolarization where
  current := p.current + q.current
  radius := p.radius + q.radius
  radius_nonneg := add_nonneg p.radius_nonneg q.radius_nonneg
  memLp := p.memLp.add q.memLp
  vanish x hx := by
    have hp := p.vanish x (by linarith [q.radius_nonneg])
    have hq := q.vanish x (by linarith [p.radius_nonneg])
    simp [hp, hq]

def vectorScalarMul : Vector →L[ℂ] ℂ →L[ℂ] Vector :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] Vector →L[ℂ] Vector).flip

theorem vectorScalarMul_apply (v : Vector) (z : ℂ) : vectorScalarMul v z = z • v := rfl

def cutoffGreen (k T : ℝ) : Position → ℂ :=
  (Metric.closedBall 0 T).indicator (outgoingGreen k)

theorem cutoffGreen_memLp (k T : ℝ) : MemLp (cutoffGreen k T) 2 volume := by
  rw [cutoffGreen, memLp_indicator_iff_restrict Metric.isClosed_closedBall.measurableSet]
  exact outgoingGreen_memLp_on_compact k _ (isCompact_closedBall _ _)

def outgoingPotential (k : ℝ) (p : CompactPolarization) : Field :=
  p.current ⋆[vectorScalarMul, volume] outgoingGreen k

theorem outgoingPotential_integrand_cutoff (k : ℝ) (p : CompactPolarization)
    (S : ℝ) (x y : Position) (hx : ‖x‖ ≤ S) :
    vectorScalarMul (p.current y) (outgoingGreen k (x - y)) =
      vectorScalarMul (p.current y) (cutoffGreen k (S + p.radius) (x - y)) := by
  classical
  by_cases hy : ‖y‖ ≤ p.radius
  · have hxy : x - y ∈ Metric.closedBall 0 (S + p.radius) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact (norm_sub_le x y).trans (add_le_add hx hy)
    simp [cutoffGreen, hxy]
  · have hp := p.vanish y (lt_of_not_ge hy)
    simp [hp]

theorem outgoingPotential_eq_cutoff (k : ℝ) (p : CompactPolarization)
    (S : ℝ) (x : Position) (hx : ‖x‖ ≤ S) :
    outgoingPotential k p x =
      (p.current ⋆[vectorScalarMul, volume] cutoffGreen k (S + p.radius)) x := by
  exact integral_congr_ae (ae_of_all _ fun y => outgoingPotential_integrand_cutoff k p S x y hx)

/-- The singular outgoing convolution exists at every point for every eligible L² current. -/
theorem outgoingPotential_integrable (k : ℝ) (p : CompactPolarization) (x : Position) :
    Integrable (fun y => outgoingGreen k (x - y) • p.current y) volume := by
  have h := ConvolutionExists.of_memLp_memLp (L := vectorScalarMul)
    p.memLp (cutoffGreen_memLp k (‖x‖ + p.radius)) x
  exact h.congr (ae_of_all _ fun y =>
    (outgoingPotential_integrand_cutoff k p ‖x‖ x y le_rfl).symm)

theorem outgoingPotential_congr_current (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : outgoingPotential k p = outgoingPotential k q := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem outgoingPotential_add (k : ℝ) (p q : CompactPolarization) :
    outgoingPotential k (p.add q) = outgoingPotential k p + outgoingPotential k q := by
  funext x
  change (∫ y : Position, outgoingGreen k (x - y) • (p.current y + q.current y)) =
    (∫ y : Position, outgoingGreen k (x - y) • p.current y) +
      (∫ y : Position, outgoingGreen k (x - y) • q.current y)
  simp_rw [smul_add]
  exact integral_add (outgoingPotential_integrable k p x) (outgoingPotential_integrable k q x)

theorem outgoingPotential_aestronglyMeasurable (k : ℝ) (p : CompactPolarization) :
    AEStronglyMeasurable (outgoingPotential k p) volume :=
  p.memLp.aestronglyMeasurable.convolution
    (L := vectorScalarMul) (outgoingGreen_measurable k).aestronglyMeasurable

def potentialBound (k : ℝ) (p : CompactPolarization) (S : ℝ) : ℝ≥0∞ :=
  ‖vectorScalarMul‖ₑ * eLpNorm p.current 2 volume *
    eLpNorm (cutoffGreen k (S + p.radius)) 2 volume

theorem potentialBound_lt_top (k : ℝ) (p : CompactPolarization) (S : ℝ) :
    potentialBound k p S < ⊤ := by
  unfold potentialBound
  finiteness [p.memLp.eLpNorm_lt_top, (cutoffGreen_memLp k (S + p.radius)).eLpNorm_lt_top]

theorem outgoingPotential_enorm_le (k : ℝ) (p : CompactPolarization)
    (S : ℝ) (x : Position) (hx : ‖x‖ ≤ S) :
    ‖outgoingPotential k p x‖ₑ ≤ potentialBound k p S := by
  rw [outgoingPotential_eq_cutoff k p S x hx]
  exact enorm_convolution_le (L := vectorScalarMul) p.memLp.aestronglyMeasurable
    (cutoffGreen_memLp k (S + p.radius)).aestronglyMeasurable x

theorem outgoingPotential_locallyIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallyIntegrable (outgoingPotential k p) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨S, hS, hKS⟩ := hK.isBounded.exists_pos_norm_lt
  apply Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (outgoingPotential_aestronglyMeasurable k p) (M := (potentialBound k p S).toReal)
  apply ae_restrict_of_forall_mem hK.measurableSet
  intro x hx
  have he := outgoingPotential_enorm_le k p S x (hKS x hx).le
  exact ENNReal.toReal_mono (potentialBound_lt_top k p S).ne he

theorem polarization_zero_outside (B : TwoLayerBody) (E : Field) (x : Position)
    (hx : x ∉ B.domain) : polarization B E x = 0 := by
  simp [polarization, susceptibility_zero_outside B x hx, tensorApply]

/-- Existing physical scattering currents belong to the convolution input class. -/
def ScatteringState.compactPolarization {k : ℝ} {B : TwoLayerBody} {σ : Direction}
    (s : ScatteringState k B σ) : CompactPolarization where
  current := polarization B s.electric
  radius := B.aperture + B.absorberThickness + B.plateThickness
  radius_nonneg := by linarith [B.aperture_pos, B.absorberThickness_pos, B.plateThickness_pos]
  memLp := s.current_memLp
  vanish x hx := by
    apply polarization_zero_outside
    intro hxd
    have hb := domain_subset_closedBall B hxd
    simp only [Metric.mem_closedBall, dist_zero_right] at hb
    exact (not_lt_of_ge hb) hx

abbrev VectorDistribution := Distribution (⊤ : TopologicalSpace.Opens Position) Vector ⊤

def potentialDistribution (k : ℝ) (p : CompactPolarization) : VectorDistribution :=
  Distribution.ofFun ⊤ (outgoingPotential k p) volume ⊤

theorem potentialDistribution_apply (k : ℝ) (p : CompactPolarization) (φ : ScalarTest) :
    potentialDistribution k p φ = ∫ x : Position, φ x • outgoingPotential k p x := by
  exact Distribution.ofFun_apply ((outgoingPotential_locallyIntegrable k p).locallyIntegrableOn _)

theorem potentialDistribution_add (k : ℝ) (p q : CompactPolarization) :
    potentialDistribution k (p.add q) = potentialDistribution k p + potentialDistribution k q := by
  unfold potentialDistribution
  rw [outgoingPotential_add]
  exact Distribution.ofFun_add
    ((outgoingPotential_locallyIntegrable k p).locallyIntegrableOn _)
    ((outgoingPotential_locallyIntegrable k q).locallyIntegrableOn _)

def vectorCoordinate (i : Fin 3) : Vector →L[ℝ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) i

def potentialComponentDistribution (k : ℝ) (p : CompactPolarization) (i : Fin 3) :
    ScalarDistribution := Distribution.mapCLM (vectorCoordinate i) (potentialDistribution k p)

theorem potentialComponentDistribution_apply (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) (φ : ScalarTest) :
    potentialComponentDistribution k p i φ =
      (∫ x : Position, φ x • outgoingPotential k p x) i := by
  rw [potentialComponentDistribution, Distribution.mapCLM_apply, potentialDistribution_apply]
  rfl

/-- Full three-dimensional volume potential `(k²I + ∇∇·)(g_k * p)`.
Distributional differentiation retains singular contact contributions. Its
representation by a bounded L² operator, and the explicit contact coefficient,
have not yet been proved. -/
def outgoingVolumeDistribution (k : ℝ) (p : CompactPolarization) (i : Fin 3) :
    ScalarDistribution :=
  (k ^ 2) • potentialComponentDistribution k p i +
    ∑ j, distributionPartial i (distributionPartial j (potentialComponentDistribution k p j))

theorem outgoingVolumeDistribution_apply (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) (φ : ScalarTest) :
    outgoingVolumeDistribution k p i φ =
      (k ^ 2) • (∫ x : Position, φ x • outgoingPotential k p x) i +
        ∑ j, (∫ x : Position, (testPartial j (testPartial i φ)) x •
          outgoingPotential k p x) j := by
  simp [outgoingVolumeDistribution, distributionPartial, testPartial,
    Distribution.lineDerivCLM_apply, potentialComponentDistribution_apply]

theorem outgoingVolumeDistribution_add (k : ℝ) (p q : CompactPolarization) (i : Fin 3) :
    outgoingVolumeDistribution k (p.add q) i =
      outgoingVolumeDistribution k p i + outgoingVolumeDistribution k q i := by
  have hc (j : Fin 3) : potentialComponentDistribution k (p.add q) j =
      potentialComponentDistribution k p j + potentialComponentDistribution k q j := by
    simp only [potentialComponentDistribution, potentialDistribution_add, map_add]
  simp only [outgoingVolumeDistribution, hc, map_add, smul_add, Finset.sum_add_distrib]
  exact add_add_add_comm _ _ _ _

end OQ7Prescribed
