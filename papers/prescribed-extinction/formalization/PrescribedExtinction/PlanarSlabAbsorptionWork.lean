import PrescribedExtinction.PlanarSlabResponseIdentification

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Classical

theorem scalarConstitutive_negative_imaginary (α z : ℂ) (hα : α ≠ 0) :
    -(inner ℂ (α * z) (α⁻¹ * (α * z))).im = α.im * Complex.normSq z := by
  rw [inv_mul_cancel_left₀ hα]
  change -(inner ℂ (α • z) z).im = _
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  change -(star α * ((‖z‖ : ℝ) : ℂ) ^ 2).im = _
  simp [Complex.mul_im, Complex.mul_re, Complex.normSq_eq_norm_sq, pow_two]

theorem slabCoupledCurrent_absorption_integral (k : ℝ) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (hα : OQ7.relativePermittivity A - 1 ≠ 0) (hβ : OQ7.relativePermittivity W - 1 ≠ 0) :
    -(inner ℂ (slabCoupledCurrent k A W θ σ hpA hpW hdA hdW)
        (planarInverseMaterial (A.width + W.width) A.width (OQ7.relativePermittivity A - 1)
          (OQ7.relativePermittivity W - 1) (slabCoupledCurrent k A W θ σ hpA hpW hdA hdW))).im =
      A.q * (∫ z in (0 : ℝ)..A.width, Complex.normSq ((slabCoupledAbsorber k A W θ σ hpA).electric z)) +
        W.q * (∫ z in A.width..(A.width + W.width), Complex.normSq ((slabCoupledPlate k A W θ σ hpW).electric z)) := by
  let L := A.width + W.width
  let F := slabCoupledAbsorber k A W θ σ hpA
  let G := slabCoupledPlate k A W θ σ hpW
  let q := slabCoupledCurrent k A W θ σ hpA hpW hdA hdW
  let α := OQ7.relativePermittivity A - 1
  let β := OQ7.relativePermittivity W - 1
  let M := planarInverseMaterial L A.width α β
  let f := (Ioc 0 A.width).indicator (fun z => A.q * Complex.normSq (F.electric z))
  let g := (Ioc A.width L).indicator (fun z => W.q * Complex.normSq (G.electric z))
  have hfc : ContinuousOn (fun z => A.q * Complex.normSq (F.electric z)) (Icc 0 A.width) :=
    continuousOn_const.mul (Complex.continuous_normSq.comp_continuousOn F.electric_continuous)
  have hgc : ContinuousOn (fun z => W.q * Complex.normSq (G.electric z)) (Icc A.width L) :=
    continuousOn_const.mul (Complex.continuous_normSq.comp_continuousOn G.electric_continuous)
  have hfi : Integrable f volume := (hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hgi : Integrable g volume := (hgc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hinner := L2.integrable_inner (𝕜 := ℂ) (q : HeightL2) (M q : HeightL2)
  have him : -(inner ℂ q (M q)).im = ∫ z : ℝ, -(inner ℂ ((q : HeightL2) z) ((M q : HeightL2) z)).im := by
    change -(inner ℂ (q : HeightL2) (M q : HeightL2)).im = _
    rw [integral_neg]
    congr 1
    rw [L2.inner_def]
    exact (Complex.imCLM.integral_comp_comm hinner).symm
  have hpoint : (fun z => -(inner ℂ ((q : HeightL2) z) ((M q : HeightL2) z)).im) =ᵐ[volume]
      fun z => f z + g z := by
    filter_upwards [slabCoupledCurrent_coe k A W θ σ hpA hpW hdA hdW,
      planarInverseMaterial_coe L A.width α β q, volume.ae_ne A.width] with z hq hm hzh
    change (q : HeightL2) z = (Ioc 0 A.width).indicator (fun t => α * F.electric t) z +
      (Ioc A.width L).indicator (fun t => β * G.electric t) z at hq
    change (M q : HeightL2) z = _ at hm
    rw [hm, hq]
    change -(inner ℂ _ (if z < A.width then α⁻¹ * _ else β⁻¹ * _)).im = f z + g z
    dsimp only [f, g]
    by_cases hzA : z < A.width
    · have hzw : z ∉ Ioc A.width L := fun hm => (not_lt_of_ge hm.1.le) hzA
      simp only [if_pos hzA, indicator_of_notMem hzw, add_zero]
      by_cases hza : z ∈ Ioc 0 A.width
      · simp only [indicator_of_mem hza]
        rw [scalarConstitutive_negative_imaginary α _ hα]
        rw [show α.im = A.q from relativePermittivity_susceptibility_im A]
      · simp only [indicator_of_notMem hza, mul_zero, inner_zero_left, Complex.zero_im, neg_zero]
    · have hza : z ∉ Ioc 0 A.width := fun hm => hzA (lt_of_le_of_ne hm.2 hzh)
      simp only [if_neg hzA, indicator_of_notMem hza, zero_add]
      by_cases hzw : z ∈ Ioc A.width L
      · simp only [indicator_of_mem hzw]
        rw [scalarConstitutive_negative_imaginary β _ hβ]
        rw [show β.im = W.q from relativePermittivity_susceptibility_im W]
      · simp only [indicator_of_notMem hzw, mul_zero, inner_zero_left, Complex.zero_im, neg_zero]
  rw [him, integral_congr_ae hpoint, integral_add hfi hgi]
  dsimp only [f, g]
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hdA,
    ← intervalIntegral.integral_of_le (show A.width ≤ L by dsimp [L]; linarith),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end OQ7Prescribed
