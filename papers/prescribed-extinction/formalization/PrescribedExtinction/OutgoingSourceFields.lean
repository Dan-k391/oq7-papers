import PrescribedExtinction.ExteriorCurrentIdentification

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem outgoingGradient_norm_le_far (k : ℝ) (j : Fin 3) (x : Position)
    (hx : 1 ≤ ‖x‖) :
    ‖outgoingGradient k j x‖ ≤ (|k| + 1) / (4 * Real.pi) := by
  have hr : 0 < ‖x‖ := by linarith
  have he : ‖Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  have hp : ‖Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 1‖ ≤ |k| * ‖x‖ + 1 := by
    simpa [norm_mul, abs_of_pos hr] using norm_sub_le (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) 1
  have hg : ‖outgoingRadialFirst k ‖x‖‖ ≤ (|k| * ‖x‖ + 1) / (4 * Real.pi * ‖x‖ ^ 2) := by
    simp only [outgoingRadialFirst, norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr.le, he, one_mul]
    norm_num [abs_of_pos Real.pi_pos]
    gcongr
  have hc : ‖x j / ‖x‖‖ ≤ 1 := by
    rw [norm_div, Real.norm_of_nonneg hr.le]
    exact (div_le_one hr).mpr (PiLp.norm_apply_le x j)
  calc
    _ ≤ ‖outgoingRadialFirst k ‖x‖‖ := by
      rw [outgoingGradient, norm_smul]
      simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ (|k| * ‖x‖ + 1) / (4 * Real.pi * ‖x‖ ^ 2) := hg
    _ ≤ ((|k| + 1) * ‖x‖) / (4 * Real.pi * ‖x‖ ^ 2) := by gcongr; nlinarith [abs_nonneg k]
    _ = ((|k| + 1) / (4 * Real.pi)) / ‖x‖ := by field_simp
    _ ≤ _ := div_le_self (by positivity) hx

theorem gradientPotential_integrable_far (k : ℝ) (p : CompactPolarization)
    (j : Fin 3) (x : Position) (hx : p.radius + 1 ≤ ‖x‖) :
    Integrable (fun y : Position => outgoingGradient k j (x - y) • p.current y) volume := by
  have hk : Measurable (fun y : Position => outgoingGradient k j (x - y)) :=
    (outgoingGradient_measurable k j).comp (measurable_const.sub measurable_id)
  have hm := hk.aestronglyMeasurable.smul p.memLp.aestronglyMeasurable
  apply ((compactPolarization_current_integrable p).norm.const_mul ((|k| + 1) / (4 * Real.pi))).mono' hm
  apply ae_of_all
  intro y
  change ‖outgoingGradient k j (x - y) • p.current y‖ ≤ _
  by_cases hy : ‖y‖ ≤ p.radius
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      (outgoingGradient_norm_le_far k j (x - y) (by linarith [norm_sub_norm_le x y])) (norm_nonneg _)
  · simp [p.vanish y (lt_of_not_ge hy)]

theorem gradientPotential_component_integral_far (k : ℝ) (p : CompactPolarization)
    (j i : Fin 3) (x : Position) (hx : p.radius + 1 ≤ ‖x‖) :
    gradientPotential k p j x i =
      ∫ y : Position, outgoingGradient k j (x - y) * p.current y i := by
  have hi := gradientPotential_integrable_far k p j x hx
  have h := ((vectorCoordinate i).integral_comp_comm hi).symm
  simpa only [gradientPotential, vectorCoordinate, PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] using h

theorem magneticExterior_eq_pointwise_far (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : p.radius + 1 ≤ ‖x‖) :
    exteriorMagnetic k p x = magneticVolumeField k p x := by
  have hg (j i : Fin 3) : Integrable (fun y : Position => outgoingGradient k j (x - y) * p.current y i) volume :=
    (vectorCoordinate i).integrable_comp (gradientPotential_integrable_far k p j x hx)
  have hm := exteriorMagnetic_integrable_far k p x hx
  ext i
  have he := ((vectorCoordinate i).integral_comp_comm hm).symm
  change exteriorMagnetic k p x i = _
  rw [show exteriorMagnetic k p x i = ∫ y : Position, kernelMagnetic k (x - y) (p.current y) i from he]
  simp_rw [kernelMagnetic_gradient]
  fin_cases i
  all_goals
    simp only [PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    simp [magneticVolumeField, potentialCurlField, PiLp.smul_apply, PiLp.add_apply, basisC,
      gradientPotential_component_integral_far k p _ _ x hx]
    rw [← integral_sub (hg _ _) (hg _ _), ← integral_const_mul]
    rw [integral_neg]

def outgoingElectricField (k : ℝ) (p : CompactPolarization) : Field := by
  classical
  exact fun x => if x ∈ currentExterior p then exteriorElectric k p x else electricVolumeField k p x

def outgoingMagneticField (k : ℝ) (p : CompactPolarization) : Field := magneticVolumeField k p

theorem outgoingElectricField_eq_ae (k : ℝ) (p : CompactPolarization) :
    outgoingElectricField k p =ᵐ[volume] electricVolumeField k p := by
  have h := (ae_restrict_iff' (currentExterior p).isOpen.measurableSet).mp (electricExterior_eq_ae k p)
  filter_upwards [h] with x hx
  unfold outgoingElectricField
  split_ifs with hmem
  · exact hx hmem
  · rfl

theorem outgoingElectricField_locallySquareIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallySquareIntegrable (outgoingElectricField k p) := by
  intro K hK
  exact (memLp_congr_ae (ae_restrict_of_ae (outgoingElectricField_eq_ae k p).symm)).mp
    (electricVolumeField_locallySquareIntegrable k p K hK)

theorem outgoingMagneticField_locallySquareIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallySquareIntegrable (outgoingMagneticField k p) :=
  magneticVolumeField_locallySquareIntegrable k p

theorem HasWeakCurl.congr_ae {F G F' G' : Field} (h : HasWeakCurl F G)
    (hF : F =ᵐ[volume] F') (hG : G =ᵐ[volume] G') : HasWeakCurl F' G' := by
  intro φ hφ hcφ
  have he : (∫ x : Position, bilinear (F' x) (curl φ x)) =
      ∫ x : Position, bilinear (F x) (curl φ x) := by
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]
  have hh : (∫ x : Position, bilinear (G x) (φ x)) =
      ∫ x : Position, bilinear (G' x) (φ x) := by
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    rw [hx]
  rw [he, h φ hφ hcφ, hh]

theorem outgoingSourceFields_first_weakCurl (k : ℝ) (p : CompactPolarization) :
    HasWeakCurl (outgoingElectricField k p)
      (fun x => (Complex.I * (k : ℂ)) • outgoingMagneticField k p x) :=
  (physicalSourceFields_first_weakCurl k p).congr_ae (outgoingElectricField_eq_ae k p).symm
    (ae_of_all _ fun _ => rfl)

theorem outgoingSourceFields_second_weakCurl (k : ℝ) (p : CompactPolarization) :
    HasWeakCurl (outgoingMagneticField k p)
      (fun x => (-Complex.I * (k : ℂ)) • (outgoingElectricField k p x + p.current x)) := by
  apply (physicalSourceFields_second_weakCurl k p).congr_ae (ae_of_all _ fun _ => rfl)
  filter_upwards [outgoingElectricField_eq_ae k p] with x hx
  rw [hx]

theorem outgoingSourceFields_outgoing (k : ℝ) (p : CompactPolarization) :
    Outgoing (outgoingElectricField k p) (outgoingMagneticField k p) := by
  intro ε hε
  obtain ⟨ρ, hρ, hbound⟩ := exteriorCurrentFields_outgoing k p ε hε
  refine ⟨max ρ (p.radius + 2), lt_of_lt_of_le hρ (le_max_left _ _), ?_⟩
  intro x hx
  have hext : x ∈ currentExterior p := by
    change p.radius + 1 < ‖x‖
    have hh := (le_max_right ρ (p.radius + 2)).trans hx
    linarith
  have hf : p.radius + 1 ≤ ‖x‖ := le_of_lt hext
  rw [outgoingElectricField, if_pos hext, outgoingMagneticField,
    ← magneticExterior_eq_pointwise_far k p x hf]
  exact hbound x ((le_max_left _ _).trans hx)

/-- Actual globally locally-L² outgoing weak-Maxwell source fields for every
original compact L² polarization. This is source solvability, before the
material volume equation and its inverse have been established. -/
theorem outgoingPhysicalSourceFields (k : ℝ) (p : CompactPolarization) :
    LocallySquareIntegrable (outgoingElectricField k p) ∧
    LocallySquareIntegrable (outgoingMagneticField k p) ∧
    HasWeakCurl (outgoingElectricField k p)
      (fun x => (Complex.I * (k : ℂ)) • outgoingMagneticField k p x) ∧
    HasWeakCurl (outgoingMagneticField k p)
      (fun x => (-Complex.I * (k : ℂ)) • (outgoingElectricField k p x + p.current x)) ∧
    Outgoing (outgoingElectricField k p) (outgoingMagneticField k p) :=
  ⟨outgoingElectricField_locallySquareIntegrable k p,
    outgoingMagneticField_locallySquareIntegrable k p,
    outgoingSourceFields_first_weakCurl k p, outgoingSourceFields_second_weakCurl k p,
    outgoingSourceFields_outgoing k p⟩

end OQ7Prescribed
