import work.PlanarSlabCoupledPotentials
import PrescribedExtinction.BodyMaterialLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem slabCoupledAbsorber_electric_eq_green (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 ≤ A.q) (hqW : 0 ≤ W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (z : ℝ) (hz : z ∈ Icc 0 A.width) :
    (slabCoupledAbsorber k A W θ σ hpA).electric z =
      (k ^ 2 : ℝ) • scalarPlanarPotential k
        (planarLayerL2Current k 0 A.width (A.width + W.width) le_rfl hdA (by linarith)
          (slabCoupledAbsorber k A W θ σ hpA) : HeightL2) z +
      (Real.cos θ : ℂ) * ((k ^ 2 : ℝ) • scalarPlanarPotential k
        (planarLayerL2Current k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl
          (slabCoupledPlate k A W θ σ hpW) : HeightL2) z) := by
  have ha := (slabAmplitudes_feedback k A W θ
    (slabFeedback_ne_zero k hk A W hpA hqA hdA hpW hqW hdW θ) σ).1
  rw [slabCoupledAbsorber_Green_interior k hk A W θ σ hpA hqA hdA hdW z hz,
    slabCoupledPlate_Green_exterior_left k hk A W θ σ hpW hqW hdA hdW z hz.2]
  linear_combination apertureOscillation k (A.width - z) * ha

theorem slabCoupledPlate_electric_eq_green (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 ≤ A.q) (hqW : 0 ≤ W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (z : ℝ) (hz : z ∈ Icc A.width (A.width + W.width)) :
    (slabCoupledPlate k A W θ σ hpW).electric z = planarIncidentPhase k σ z +
      (Real.cos θ : ℂ) * ((k ^ 2 : ℝ) • scalarPlanarPotential k
        (planarLayerL2Current k 0 A.width (A.width + W.width) le_rfl hdA (by linarith)
          (slabCoupledAbsorber k A W θ σ hpA) : HeightL2) z) +
      (k ^ 2 : ℝ) • scalarPlanarPotential k
        (planarLayerL2Current k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl
          (slabCoupledPlate k A W θ σ hpW) : HeightL2) z := by
  have ha := (slabAmplitudes_feedback k A W θ
    (slabFeedback_ne_zero k hk A W hpA hqA hdA hpW hqW hdW θ) σ).2
  rw [slabCoupledAbsorber_Green_exterior_right k hk A W θ σ hpA hqA hdA hdW z hz.1,
    slabCoupledPlate_Green_interior k hk A W θ σ hpW hqW hdA hdW z hz,
    ← slabAuxiliaryIncident_phase k A W σ z]
  linear_combination apertureOscillation k (z - A.width) * ha

theorem slabCoupledCurrent_coe (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) :
    (slabCoupledCurrent k A W θ σ hpA hpW hdA hdW : HeightL2) =ᵐ[volume]
      fun z => (Ioc 0 A.width).indicator (fun t => (OQ7.relativePermittivity A - 1) *
          (slabCoupledAbsorber k A W θ σ hpA).electric t) z +
        (Ioc A.width (A.width + W.width)).indicator (fun t => (OQ7.relativePermittivity W - 1) *
          (slabCoupledPlate k A W θ σ hpW).electric t) z := by
  let F := slabCoupledAbsorber k A W θ σ hpA
  let G := slabCoupledPlate k A W θ σ hpW
  let qA := planarLayerL2Current k 0 A.width (A.width + W.width) le_rfl hdA (by linarith) F
  let qW := planarLayerL2Current k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl G
  have hF : F.current = fun z => (OQ7.relativePermittivity A - 1) * F.electric z :=
    funext (slabCoupledAbsorber_constitutive k A W θ σ hpA)
  have hG : G.current = fun z => (OQ7.relativePermittivity W - 1) * G.electric z :=
    funext (slabCoupledPlate_constitutive k A W θ σ hpW)
  filter_upwards [Lp.coeFn_add (qA : HeightL2) (qW : HeightL2),
    planarLayerL2Current_coe k 0 A.width (A.width + W.width) le_rfl hdA (by linarith) F,
    planarLayerL2Current_coe k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl G] with z ha hqa hqw
  change ((qA : HeightL2) + (qW : HeightL2)) z = _
  rw [ha]
  change (qA : HeightL2) z + (qW : HeightL2) z = _
  rw [hqa, hqw, hF, hG]

theorem slabCoupledCurrent_material_equation (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 ≤ A.q) (hqW : 0 ≤ W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (hα : OQ7.relativePermittivity A - 1 ≠ 0) (hβ : OQ7.relativePermittivity W - 1 ≠ 0) :
    planarActiveMaterialOperator k hk (A.width + W.width) (by linarith) A.width θ
      (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
      (slabCoupledCurrent k A W θ σ hpA hpW hdA hdW) = -planarNormalizedDrive k σ (A.width + W.width) A.width := by
  let L := A.width + W.width
  have hL : A.width ≤ L := by dsimp [L]; linarith
  let F := slabCoupledAbsorber k A W θ σ hpA
  let G := slabCoupledPlate k A W θ σ hpW
  let q := slabCoupledCurrent k A W θ σ hpA hpW hdA hdW
  let α := OQ7.relativePermittivity A - 1
  let β := OQ7.relativePermittivity W - 1
  let T := planarActiveOutgoing k hk L (hdA.trans hL) A.width θ
  let M := planarInverseMaterial L A.width α β
  let g := planarNormalizedDrive k σ L A.width
  have hT := planarActiveOutgoing_two_layer_current_coe k hk A.width L hdA hL θ F G
  have hM := planarInverseMaterial_coe L A.width α β q
  have hq := slabCoupledCurrent_coe k A W θ σ hpA hpW hdA hdW
  have hg := planarNormalizedDrive_coe k σ L A.width
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hT, hM, hq, hg, Lp.coeFn_sub (T q : HeightL2) (M q : HeightL2),
    Lp.coeFn_neg (g : HeightL2), volume.ae_ne (0 : ℝ), volume.ae_ne A.width] with z ht hm hqz hgz hsub hneg hz0 hzh
  change ((T q : HeightL2) - (M q : HeightL2)) z = (-(g : HeightL2) : HeightL2) z
  rw [hsub, hneg]
  change (T q : HeightL2) z - (M q : HeightL2) z = -(g : HeightL2) z
  change (T q : HeightL2) z = _ at ht
  change (M q : HeightL2) z = _ at hm
  change (g : HeightL2) z = _ at hgz
  change (q : HeightL2) z = (Ioc 0 A.width).indicator (fun t => α * F.electric t) z +
    (Ioc A.width L).indicator (fun t => β * G.electric t) z at hqz
  rw [ht, hm, hgz]
  change (Icc 0 L).indicator _ z -
    (if z < A.width then α⁻¹ * (q : HeightL2) z else β⁻¹ * (q : HeightL2) z) =
    -(Icc 0 L).indicator (fun z => if z < A.width then 0 else planarIncidentPhase k σ z) z
  rw [hqz]
  by_cases hz : z ∈ Icc 0 L
  · simp only [indicator_of_mem hz]
    by_cases hzA : z < A.width
    · have hza : z ∈ Ioc 0 A.width := ⟨lt_of_le_of_ne hz.1 hz0.symm, hzA.le⟩
      have hzw : z ∉ Ioc A.width L := fun hm => (not_lt_of_ge hm.1.le) hzA
      simp only [if_pos hzA, indicator_of_mem hza, indicator_of_notMem hzw, add_zero, neg_zero]
      rw [inv_mul_cancel_left₀ (show α ≠ 0 from hα)]
      have he := slabCoupledAbsorber_electric_eq_green k hk A W θ σ hpA hpW hqA hqW hdA hdW z ⟨hz.1, hzA.le⟩
      rw [← he]
      exact sub_self _
    · have hza : z ∉ Ioc 0 A.width := fun hm => hzA (lt_of_le_of_ne hm.2 hzh)
      have hzw : z ∈ Ioc A.width L := ⟨lt_of_le_of_ne (not_lt.mp hzA) hzh.symm, hz.2⟩
      simp only [if_neg hzA, indicator_of_notMem hza, indicator_of_mem hzw, zero_add]
      rw [inv_mul_cancel_left₀ (show β ≠ 0 from hβ)]
      have he := slabCoupledPlate_electric_eq_green k hk A W θ σ hpA hpW hqA hqW hdA hdW z ⟨(not_lt.mp hzA), hz.2⟩
      change _ - G.electric z = -planarIncidentPhase k σ z
      rw [he]
      ring
  · have hza : z ∉ Ioc 0 A.width := fun hm => hz ⟨hm.1.le, hm.2.trans hL⟩
    have hzw : z ∉ Ioc A.width L := fun hm => hz ⟨hdA.trans hm.1.le, hm.2⟩
    simp only [indicator_of_notMem hz, indicator_of_notMem hza, indicator_of_notMem hzw,
      add_zero, mul_zero, ite_self, sub_self, neg_zero]

end OQ7Prescribed
