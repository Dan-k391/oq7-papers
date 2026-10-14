import work.RotationContinuity
import PrescribedExtinction.PhysicalOpticalBalance

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory
local notation "ScalarL2" => Lp ℂ 2 (volume : Measure Position)

private theorem normalizedWork_scalar_algebra (k t a : ℝ) :
    k * (t - a) = k * -a + k * t := by ring

theorem bodyPlateInterior_nonempty (B : TwoLayerBody) :
    (B.domain ∩ {x : Position | B.absorberThickness < x 2}).Nonempty := by
  refine ⟨WithLp.toLp 2 ![0, 0, B.absorberThickness + B.plateThickness / 2], ?_⟩
  change _ ∈ B.domain ∧ _
  change ((-B.aperture / 2 < 0 ∧ 0 < B.aperture / 2 ∧
    -B.aperture / 2 < 0 ∧ 0 < B.aperture / 2) ∧
    0 < B.absorberThickness + B.plateThickness / 2 ∧
    B.absorberThickness + B.plateThickness / 2 < B.absorberThickness + B.plateThickness) ∧
    B.absorberThickness < B.absorberThickness + B.plateThickness / 2
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;>
    linarith [B.aperture_pos, B.absorberThickness_pos, B.plateThickness_pos]

theorem bodyPlateInterior_volume_pos (B : TwoLayerBody) :
    0 < volume (B.domain ∩ {x : Position | B.absorberThickness < x 2}) := by
  have hc : Continuous (fun x : Position => x 2) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Position →L[ℝ] ℝ).continuous
  exact ((bodyDomain_isOpen B).inter (isOpen_lt continuous_const hc)).measure_pos volume
    (bodyPlateInterior_nonempty B)

theorem normalizedIncidentDrive_ne_zero (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    normalizedIncidentDrive k B σ ≠ 0 := by
  intro hz
  have hae : ∀ᵐ x ∂(volume : Measure Position),
      x ∉ B.domain ∩ {x : Position | B.absorberThickness < x 2} := by
    filter_upwards [normalizedIncidentDrive_coe k B σ, Lp.coeFn_zero ℂ 2 (volume : Measure Position)] with x hx hzero
    intro hxs
    have hphase : planePhase k σ x = 0 := by
      rw [hz] at hx
      change (0 : ScalarL2) x = _ at hx
      rw [hzero, indicator_of_mem hxs.1, if_neg (not_lt.mpr (le_of_lt hxs.2))] at hx
      exact hx.symm
    have hn := planePhase_norm k σ x
    rw [hphase, norm_zero] at hn
    norm_num at hn
  have hnull := measure_eq_zero_iff_ae_notMem.mpr hae
  have hp := bodyPlateInterior_volume_pos B
  rw [hnull] at hp
  exact (lt_irrefl _ hp)

theorem normalizedActiveResponse_equation (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    activeMaterialOperator k B (basisR 0) (rotatedAxis θ) α β
      (normalizedActiveResponse k hk B σ θ α β hα hβ) = -normalizedIncidentDrive k B σ := by
  exact (activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ).apply_symm_apply _

theorem normalizedActiveResponse_ne_zero (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedActiveResponse k hk B σ θ α β hα hβ ≠ 0 := by
  intro hz
  have he := normalizedActiveResponse_equation k hk B σ θ α β hα hβ
  rw [hz, map_zero] at he
  exact normalizedIncidentDrive_ne_zero k B σ (neg_eq_zero.mp he.symm)

theorem normalizedAbsorption_pos (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    0 < normalizedAbsorption k hk B σ θ α β hα hβ := by
  have hc := activeMaterialCoercivity_pos α β hα hβ
  have hr := norm_pos_iff.mpr (normalizedActiveResponse_ne_zero k hk B σ θ α β hα hβ)
  have hl := activeInverseMaterial_negative_imaginary_bound B α β
    (normalizedActiveResponse k hk B σ θ α β hα hβ)
  exact mul_pos hk ((mul_pos hc (sq_pos_of_pos hr)).trans_le hl)

theorem normalizedExtinction_work_balance (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedExtinction k hk B σ θ α β hα hβ =
      normalizedAbsorption k hk B σ θ α β hα hβ + k *
        (inner ℂ (activeInjection B (basisR 0) (rotatedAxis θ)
          (normalizedActiveResponse k hk B σ θ α β hα hβ))
          (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ)
            (normalizedActiveResponse k hk B σ θ α β hα hβ)))).im := by
  let r := normalizedActiveResponse k hk B σ θ α β hα hβ
  have he := normalizedActiveResponse_equation k hk B σ θ α β hα hβ
  change activeProjection B (basisR 0) (rotatedAxis θ)
    (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) r)) -
      activeInverseMaterial B α β r = -normalizedIncidentDrive k B σ at he
  have hi := congrArg (fun z => (inner ℂ r z).im) he
  rw [inner_sub_right, inner_neg_right, Complex.sub_im, Complex.neg_im] at hi
  have hj := activeInjection_inner B (basisR 0) (rotatedAxis θ) r
    (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) r))
  rw [← hj] at hi
  have hs := inner_im_symm (𝕜 := ℂ) (normalizedIncidentDrive k B σ) r
  have hsum : (inner ℂ (normalizedIncidentDrive k B σ) r).im =
      (inner ℂ (activeInjection B (basisR 0) (rotatedAxis θ) r)
        (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) r))).im -
      (inner ℂ r (activeInverseMaterial B α β r)).im := hs.trans hi.symm
  change k * (inner ℂ (normalizedIncidentDrive k B σ) r).im =
    k * -(inner ℂ r (activeInverseMaterial B α β r)).im + k *
      (inner ℂ (activeInjection B (basisR 0) (rotatedAxis θ) r)
        (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) r))).im
  calc
    _ = k * ((inner ℂ (activeInjection B (basisR 0) (rotatedAxis θ) r)
        (bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ) r))).im -
      (inner ℂ r (activeInverseMaterial B α β r)).im) :=
        congrArg (fun z : ℝ => k * z) hsum
    _ = _ := normalizedWork_scalar_algebra k _ _

theorem normalizedAbsorption_le_extinction (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedAbsorption k hk B σ θ α β hα hβ ≤ normalizedExtinction k hk B σ θ α β hα hβ := by
  rw [normalizedExtinction_work_balance]
  exact le_add_of_nonneg_right (mul_nonneg hk.le (bodyOutgoingOperator_im_nonneg k hk B _))

theorem normalizedExtinction_pos (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    0 < normalizedExtinction k hk B σ θ α β hα hβ :=
  (normalizedAbsorption_pos k hk B σ θ α β hα hβ).trans_le
    (normalizedAbsorption_le_extinction k hk B σ θ α β hα hβ)

theorem physicalScattering_sine_squared_factorization (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    scattering k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
      (volumeTotalElectric k σ (bodyCurrentPolarization B
        (activeInjection B (basisR 0) (rotatedAxis θ)
          (activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ)))) =
      (Real.sin θ) ^ 2 * (normalizedExtinction k hk B σ θ α β hα hβ -
        normalizedAbsorption k hk B σ θ α β hα hβ) := by
  have he := physicalVolume_energy_balance k (rankOneBody B (basisR 0) (rotatedAxis θ) α β) σ
    (activeInjection B (basisR 0) (rotatedAxis θ)
      (activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ))
    (activePhysicalSolution_physicalVolumeEquation k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ)
  change extinction k (rankOneBody B (basisR 0) (rotatedAxis θ) α β) σ
    (volumeTotalElectric k σ (bodyCurrentPolarization B _)) =
      absorption k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
        (volumeTotalElectric k σ (bodyCurrentPolarization B _)) +
      scattering k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
        (volumeTotalElectric k σ (bodyCurrentPolarization B _)) at he
  rw [physicalExtinction_sine_squared_factorization, physicalAbsorption_sine_squared_factorization] at he
  linarith

end OQ7Prescribed
