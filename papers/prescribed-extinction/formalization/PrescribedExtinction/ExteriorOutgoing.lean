import PrescribedExtinction.RadiationKernel

/-! Actual classical exterior Green-current convolutions. Their outgoing
condition will be established directly from the uniform kernel estimate.
Equality with the global L² electric representative is a separate obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem radialDirection_norm (x : Position) (hx : x ≠ 0) : ‖radialDirection x‖ = 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [radialDirection, norm_smul, hn]

def crossRightLinear (n : Vector) : Vector →ₗ[ℂ] Vector where
  toFun := fun v => cross v n
  map_add' u v := by
    ext i
    fin_cases i <;> simp [cross, PiLp.add_apply] <;> ring
  map_smul' a v := by
    ext i
    fin_cases i <;> simp [cross, PiLp.smul_apply] <;> ring

def crossRightMap (n : Vector) : Vector →L[ℂ] Vector :=
  (crossRightLinear n).mkContinuous ‖n‖ fun v => by
    simpa [crossRightLinear, mul_comm] using cross_norm_le v n

theorem crossRightMap_apply (n v : Vector) : crossRightMap n v = cross v n := rfl

theorem kernelMagnetic_norm_le_far (k : ℝ) (x : Position) (hx : 1 ≤ ‖x‖) (v : Vector) :
    ‖kernelMagnetic k x v‖ ≤ (|k| * (|k| + 1) / (4 * Real.pi)) * ‖v‖ := by
  have hn : x ≠ 0 := norm_pos_iff.mp (by linarith)
  apply (kernelMagnetic_norm_le k x hn v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  calc
    _ ≤ |k| * ((|k| + 1) * ‖x‖) / (4 * Real.pi * ‖x‖ ^ 2) := by gcongr; nlinarith [abs_nonneg k]
    _ = (|k| * (|k| + 1) / (4 * Real.pi)) / ‖x‖ := by field_simp
    _ ≤ _ := div_le_self (by positivity) hx

def exteriorKernelBound (k : ℝ) : ℝ := (|k| * (|k| + 1) + 2 * |k| + 4) / (4 * Real.pi)

theorem classicalDyadic_norm_le_far (k : ℝ) (x : Position) (hx : 1 ≤ ‖x‖) (v : Vector) :
    ‖classicalDyadic k x v‖ ≤ exteriorKernelBound k * ‖v‖ := by
  have hn : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hr : ‖complexify (radialDirection x)‖ = 1 := by rw [complexify_norm, radialDirection_norm x hn]
  have h2 : 1 ≤ ‖x‖ ^ 2 := one_le_pow₀ hx
  have h3 : 1 ≤ ‖x‖ ^ 3 := one_le_pow₀ hx
  have hd : ‖cross (kernelMagnetic k x v) (complexify (radialDirection x)) - classicalDyadic k x v‖ ≤
      ((2 * |k| + 4) / (4 * Real.pi)) * ‖v‖ := by
    apply (kernel_radiation_defect_norm_le k x hn v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    calc
      _ ≤ 2 * |k| / (4 * Real.pi) + 1 / Real.pi := by
        apply add_le_add
        · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          simpa using mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * Real.pi by positivity)
        · apply div_le_div_of_nonneg_left (by positivity) Real.pi_pos
          simpa using mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
      _ = _ := by field_simp
  calc
    _ ≤ ‖cross (kernelMagnetic k x v) (complexify (radialDirection x))‖ +
      ‖cross (kernelMagnetic k x v) (complexify (radialDirection x)) - classicalDyadic k x v‖ := by
        simpa [norm_sub_rev] using norm_le_norm_add_norm_sub
          (cross (kernelMagnetic k x v) (complexify (radialDirection x))) (classicalDyadic k x v)
    _ ≤ ‖kernelMagnetic k x v‖ +
      ((2 * |k| + 4) / (4 * Real.pi)) * ‖v‖ := by
        gcongr
        simpa [hr] using cross_norm_le (kernelMagnetic k x v) (complexify (radialDirection x))
    _ ≤ (|k| * (|k| + 1) / (4 * Real.pi)) * ‖v‖ +
      ((2 * |k| + 4) / (4 * Real.pi)) * ‖v‖ := by gcongr; exact kernelMagnetic_norm_le_far k x hx v
    _ = _ := by unfold exteriorKernelBound; ring

def exteriorElectric (k : ℝ) (p : CompactPolarization) : Field :=
  fun x => ∫ y : Position, classicalDyadic k (x - y) (p.current y)

def exteriorMagnetic (k : ℝ) (p : CompactPolarization) : Field :=
  fun x => ∫ y : Position, kernelMagnetic k (x - y) (p.current y)

theorem exteriorElectric_integrable_far (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : p.radius + 1 ≤ ‖x‖) :
    Integrable (fun y => classicalDyadic k (x - y) (p.current y)) volume := by
  have hm := p.memLp.aestronglyMeasurable.convolution_integrand_snd vectorOperatorApply
    (classicalDyadic_measurable k).aestronglyMeasurable x
  apply ((compactPolarization_current_integrable p).norm.const_mul (exteriorKernelBound k)).mono' hm
  apply ae_of_all
  intro y
  by_cases hy : ‖y‖ ≤ p.radius
  · exact classicalDyadic_norm_le_far k (x - y) (by linarith [norm_sub_norm_le x y]) _
  · simp [p.vanish y (lt_of_not_ge hy)]

theorem exteriorMagnetic_integrable_far (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : p.radius + 1 ≤ ‖x‖) :
    Integrable (fun y => kernelMagnetic k (x - y) (p.current y)) volume := by
  have hcross : Continuous (fun q : Vector × Vector => cross q.1 q.2) := by unfold cross; fun_prop
  have hpos : AEStronglyMeasurable (fun y : Position => complexify (x - y)) volume := by
    have hm : Measurable (fun y : Position => complexify (x - y)) := by unfold complexify; fun_prop
    exact hm.aestronglyMeasurable
  have ha : AEStronglyMeasurable (fun y : Position =>
      -Complex.I * (k : ℂ) * outgoingRadialFirst k ‖x - y‖ / (‖x - y‖ : ℂ)) volume := by
    have hm : Measurable (fun y : Position =>
      -Complex.I * (k : ℂ) * outgoingRadialFirst k ‖x - y‖ / (‖x - y‖ : ℂ)) := by
      unfold outgoingRadialFirst
      fun_prop
    exact hm.aestronglyMeasurable
  have hm := ha.smul (hcross.comp_aestronglyMeasurable (hpos.prodMk p.memLp.aestronglyMeasurable))
  apply ((compactPolarization_current_integrable p).norm.const_mul
    (|k| * (|k| + 1) / (4 * Real.pi))).mono' hm
  apply ae_of_all
  intro y
  by_cases hy : ‖y‖ ≤ p.radius
  · exact kernelMagnetic_norm_le_far k (x - y) (by linarith [norm_sub_norm_le x y]) _
  · simp [kernelMagnetic, p.vanish y (lt_of_not_ge hy), cross]

theorem exterior_radiation_integral_norm_le (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : 2 * p.radius + 2 ≤ ‖x‖) :
    ‖cross (exteriorMagnetic k p x) (complexify (radialDirection x)) - exteriorElectric k p x‖ ≤
      radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖ := by
  have hxf : p.radius + 1 ≤ ‖x‖ := by linarith [p.radius_nonneg]
  have hm := exteriorMagnetic_integrable_far k p x hxf
  have he := exteriorElectric_integrable_far k p x hxf
  let T := crossRightMap (complexify (radialDirection x))
  have ht : Integrable (fun y : Position => cross (kernelMagnetic k (x - y) (p.current y))
      (complexify (radialDirection x))) volume := T.integrable_comp hm
  have hid : cross (exteriorMagnetic k p x) (complexify (radialDirection x)) - exteriorElectric k p x =
      ∫ y : Position, cross (kernelMagnetic k (x - y) (p.current y))
        (complexify (radialDirection x)) - classicalDyadic k (x - y) (p.current y) := by
    change T (∫ y : Position, kernelMagnetic k (x - y) (p.current y)) - _ = _
    rw [← T.integral_comp_comm hm]
    change (∫ y : Position, cross (kernelMagnetic k (x - y) (p.current y))
      (complexify (radialDirection x))) - (∫ y : Position, classicalDyadic k (x - y) (p.current y)) = _
    exact (integral_sub ht he).symm
  rw [hid]
  calc
    _ ≤ ∫ y : Position, (radiationKernelConstant k p.radius / ‖x‖ ^ 2) * ‖p.current y‖ := by
      apply norm_integral_le_of_norm_le ((compactPolarization_current_integrable p).norm.const_mul _)
      apply ae_of_all
      intro y
      by_cases hy : ‖y‖ ≤ p.radius
      · exact displaced_kernel_radiation_norm_le k p.radius p.radius_nonneg x y hx hy _
      · simp [kernelMagnetic, cross, p.vanish y (lt_of_not_ge hy)]
    _ = _ := integral_const_mul _ _

/-- The actual exterior dyadic/current integrals satisfy the full uniform
Silver--Müller condition. Integrability in the far zone is proved above. -/
theorem exteriorCurrentFields_outgoing (k : ℝ) (p : CompactPolarization) :
    Outgoing (exteriorElectric k p) (exteriorMagnetic k p) := by
  intro ε hε
  have hR := p.radius_nonneg
  let C := radiationKernelConstant k p.radius * ∫ y : Position, ‖p.current y‖
  have hC : 0 ≤ C := by
    unfold C radiationKernelConstant
    positivity
  let ρ := 2 * p.radius + 3 + C / ε
  have hρ : 0 < ρ := by unfold ρ; positivity
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  have hxf : 2 * p.radius + 2 ≤ ‖x‖ := by
    have hc : 0 ≤ C / ε := div_nonneg hC hε.le
    dsimp [ρ] at hx
    linarith
  have hn : 0 < ‖x‖ := hρ.trans_le hx
  have hb := exterior_radiation_integral_norm_le k p x hxf
  have hstrict : C / ‖x‖ < ε := (div_lt_iff₀ hn).mpr (by
    have hc : C / ε < ‖x‖ := by dsimp [ρ] at hx; linarith [p.radius_nonneg]
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hc)
  calc
    _ ≤ ‖x‖ * (radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖) :=
      mul_le_mul_of_nonneg_left hb hn.le
    _ = C / ‖x‖ := by unfold C; field_simp
    _ < ε := hstrict

end OQ7Prescribed
