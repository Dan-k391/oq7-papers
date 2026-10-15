import QuarticMaxwell.VolumeInverse
import QuarticMaxwell.Operator

/-! Exact quartic contrast for the actual measurable-support tensor volume
problem. Every operator/source/power estimate used by the scalar chain is
derived from the literal pointwise material and support hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QuarticMaxwell
namespace UniformBound
open MeasureTheory Set OQ7Prescribed

def absorptionPower {D : Set Position} (k : ℝ) (W : DomainL2 D →L[ℂ] DomainL2 D)
    (p : DomainL2 D) : ℝ := -k * (inner ℂ p (W p)).im

def scatteringPower {D : Set Position} (k : ℝ) (F : DomainL2 D →L[ℂ] Lp Vector 2 sphereArea)
    (p : DomainL2 D) : ℝ := k ^ 4 / (16 * Real.pi ^ 2) * ‖F p‖ ^ 2

def extinctionPower {D : Set Position} (k : ℝ) (A : DomainL2 D ≃L[ℂ] DomainL2 D)
    (f : DomainL2 D) : ℝ := -k * (inner ℂ (A.symm f) f).im

theorem extinction_pos {D : Set Position} (A : DomainL2 D ≃L[ℂ] DomainL2 D)
    {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ)
    (hc : ∀ p, ‖p‖ ^ 2 / ρ ≤ -(inner ℂ p (A p)).im)
    (f : DomainL2 D) (hf : f ≠ 0) : 0 < extinctionPower k A f := by
  have hp : A.symm f ≠ 0 := by
    intro hp
    have h := A.apply_symm_apply f
    rw [hp, map_zero] at h
    exact hf h.symm
  have h := hc (A.symm f)
  rw [A.apply_symm_apply] at h
  have hn : 0 < ‖A.symm f‖ ^ 2 / ρ := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hp)) hρ
  have hx := mul_pos hk (lt_of_lt_of_le hn h)
  unfold extinctionPower
  nlinarith

variable (D : Set Position) (hD : MeasurableSet D)
  (χ : Position → Vector →L[ℂ] Vector) (hχ : AEStronglyMeasurable χ volume)
  (M : ℝ) (hcap : ∀ᵐ x ∂volume, x ∈ D → ‖χ x‖ ≤ M)
  {m : ℝ} (hm : 0 < m)
  (hloss : ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector, m * ‖v‖ ^ 2 ≤ (inner ℂ v (χ x v)).im)

/-- The manuscript's exact uniform upper bound for the two actual volume
solutions. Absorption uses the constructed inverse susceptibility, and its
energy balance with the complete physical far-field power is proved inside. -/
theorem uniform_quartic_contrast {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    (hfin : volume D ≠ ⊤) (hV : 0 < volume.real D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1) :
    let A := VolumeInverse.equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub
    let W := VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss
    let f := domainIncidentSource k n e D hD hfin
    let g := domainIncidentSource (-k) n e D hD hfin
    let X := extinctionPower k A f
    0 < X ∧
      |absorptionPower k W (A.symm f) - absorptionPower k W (A.symm g)| / X ≤
        min 1 (2 / (3 * Real.pi) * (M ^ 2 / m) ^ 2 *
          (1 / m + 1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2) *
          k ^ 4 * R * volume.real D) := by
  let A := VolumeInverse.equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub
  let W := VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss
  let K := domainOutgoingOperator k D hD hR hsub
  let F := domainRadiationMap k D hD hfin
  let f := domainIncidentSource k n e D hD hfin
  let g := domainIncidentSource (-k) n e D hD hfin
  let X := extinctionPower k A f
  let ρ := M ^ 2 / m
  let L := 1 / m + 1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hc (p : DomainL2 D) : ‖p‖ ^ 2 / ρ ≤ -(inner ℂ p (A p)).im := by
    have h := VolumeInverse.negative_coercive D hD χ hχ M hcap hm hloss hk hM hfin hR hsub p
    change ‖p‖ ^ 2 / (M ^ 2 / m) ≤ _
    have heq : ‖p‖ ^ 2 / (M ^ 2 / m) = m / M ^ 2 * ‖p‖ ^ 2 := by field_simp
    rw [heq]
    exact h
  have hf : ‖f‖ ^ 2 = volume.real D := by
    simpa [f, hen] using domainIncidentSource_norm_sq k n e D hD hfin
  have hfne : f ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hf
    linarith
  have hX : 0 < X := extinction_pos A hk hρ hc f hfne
  have hArec (p q : DomainL2 D) : inner ℂ (domainConjugate D p) (A q) =
      inner ℂ (domainConjugate D q) (A p) :=
    VolumeInverse.operator_reciprocity D hD χ hχ M hcap hm hloss hk hsym hR hsub p q
  have hfgconj : domainConjugate D f = g := domainIncidentSource_conjugate k n e he D hD hfin
  have hforward := domain_conjugate_pair_common_work D A hArec f
  rw [hfgconj] at hforward
  have hcommon : extinctionPower k A f = extinctionPower k A g := by
    have hp := inner_im_symm (𝕜 := ℂ) (A.symm f) f
    have hq := inner_im_symm (𝕜 := ℂ) (A.symm g) g
    have hi := congrArg Complex.im hforward
    change (inner ℂ (A.symm f) f).im = -(inner ℂ f (A.symm f)).im at hp
    change (inner ℂ (A.symm g) g).im = -(inner ℂ g (A.symm g)).im at hq
    unfold extinctionPower
    rw [hp, hq, hi]
  have hbalance (u : DomainL2 D) : extinctionPower k A u =
      absorptionPower k W (A.symm u) + scatteringPower k F (A.symm u) := by
    have heq : W (A.symm u) - K (A.symm u) = u := A.apply_symm_apply u
    have hi := congrArg (fun v : DomainL2 D => (inner ℂ (A.symm u) v).im) heq
    simp only [inner_sub_right, Complex.sub_im] at hi
    have hw := domainOutgoingOperator_radiation_work k D hD hfin hR hsub (A.symm u)
    change k * (inner ℂ (A.symm u) (K (A.symm u))).im =
      scatteringPower k F (A.symm u) at hw
    unfold extinctionPower absorptionPower
    nlinarith
  have hapos (u : DomainL2 D) : 0 ≤ absorptionPower k W (A.symm u) := by
    have h := TensorMultiplier.inverse_loss_bound volume D χ hχ M hcap hD hm hloss hM (A.symm u)
    change m / M ^ 2 * ‖A.symm u‖ ^ 2 ≤ -(inner ℂ (A.symm u) (W (A.symm u))).im at h
    have hneg : 0 ≤ -(inner ℂ (A.symm u) (W (A.symm u))).im :=
      (show 0 ≤ m / M ^ 2 * ‖A.symm u‖ ^ 2 by positivity).trans h
    unfold absorptionPower
    nlinarith [mul_nonneg hk.le hneg]
  have hspos (u : DomainL2 D) : 0 ≤ scatteringPower k F (A.symm u) := by
    unfold scatteringPower
    positivity
  have hpbal := hbalance f
  have hqbal := hbalance g
  have hApX : absorptionPower k W (A.symm f) ≤ X := by dsimp [X]; linarith [hspos f]
  have hAmX : absorptionPower k W (A.symm g) ≤ X := by dsimp [X]; linarith [hspos g]
  have hone := normalized_absorption_difference_le_one hX (hapos f) (hapos g) hApX hAmX
  have hsource : ‖f - g‖ ≤ 2 * k * R * ‖f‖ := by
    have hs := domainIncidentSource_opposite_norm_sq k hk.le n e D hD hfin hR hsub
    have hs' : ‖f - g‖ ^ 2 ≤ 4 * k ^ 2 * R ^ 2 * ‖f‖ ^ 2 := by
      rw [hf]
      simpa only [hen, one_pow, mul_one] using hs
    have heq : (2 * k * R * ‖f‖) ^ 2 = 4 * k ^ 2 * R ^ 2 * ‖f‖ ^ 2 := by ring
    nlinarith [norm_nonneg (f - g), mul_nonneg (show 0 ≤ 2 * k * R by positivity) (norm_nonneg f)]
  have hbound := shared_inverse_quartic_bound A F hk hR hV.le hρ hL hX
    (VolumeInverse.operator_norm_le D hD χ hχ M hcap hm hloss hk.le hR hsub hV)
    (VolumeInverse.inverse_norm_le D hD χ hχ M hcap hm hloss hk hM hfin hR hsub)
    hc (domainRadiationMap_norm_sq_le k D hD hfin) f g hsource rfl hcommon
  have habs : |absorptionPower k W (A.symm f) - absorptionPower k W (A.symm g)| =
      |k ^ 4 / (16 * Real.pi ^ 2) * (‖F (A.symm f)‖ ^ 2 - ‖F (A.symm g)‖ ^ 2)| := by
    rw [← abs_neg]
    congr 1
    have heq : absorptionPower k W (A.symm f) - absorptionPower k W (A.symm g) =
      -(scatteringPower k F (A.symm f) - scatteringPower k F (A.symm g)) := by linarith
    rw [heq]
    unfold scatteringPower
    ring
  change 0 < X ∧ _
  refine ⟨hX, le_min hone ?_⟩
  rw [habs]
  exact hbound

end UniformBound
end QuarticMaxwell
