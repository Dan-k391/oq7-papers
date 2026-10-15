import GeneralizedResearch.ScalarContrast
import GeneralizedResearch.ScalarPhase

/-! Physical approach to the scalar golden-ratio contrast. The exact-target
multilayer sequence is OQ7.sharp_physical_constructed_sequence. A proved
bounded-index reflectionless slab corrects the actual vacuum-reference phase;
all loss, power targets and geometric thickness remain accounted for. -/
noncomputable section
namespace GeneralizedResearch
namespace ScalarPhysicalSharpness
open OQ7 ScalarContrast ScalarPhase Filter
open scoped Topology ComplexOrder

def targetT : ℝ := goldenQ ^ 4
def targetA : ℝ := 4 * goldenQ - 2
def targetX : ℝ := 2 * (1 - goldenQ ^ 2)
def stackExtinction (k : ℝ) (layers : List HomogeneousLayer) : ℝ :=
  extinction (referenceTransmission k layers)

theorem golden_recurrence (n : ℕ) : goldenQ ^ (n + 2) = goldenQ ^ n - goldenQ ^ (n + 1) := by
  linear_combination (goldenQ ^ n) * golden_properties.2.2.1

theorem golden_powers : goldenQ ^ 2 = 1 - goldenQ ∧ goldenQ ^ 3 = 2 * goldenQ - 1 ∧
    goldenQ ^ 4 = 2 - 3 * goldenQ ∧ goldenQ ^ 5 = 5 * goldenQ - 3 ∧
    goldenQ ^ 6 = 5 - 8 * goldenQ ∧ goldenQ ^ 7 = 13 * goldenQ - 8 ∧
    goldenQ ^ 8 = 13 - 21 * goldenQ ∧ goldenQ ^ 9 = 34 * goldenQ - 21 ∧
    goldenQ ^ 10 = 34 - 55 * goldenQ := by
  have h2 : goldenQ ^ 2 = 1 - goldenQ := by linarith [golden_properties.2.2.1]
  have h3 : goldenQ ^ 3 = 2 * goldenQ - 1 := by nlinarith [golden_recurrence 1]
  have h4 : goldenQ ^ 4 = 2 - 3 * goldenQ := by nlinarith [golden_recurrence 2]
  have h5 : goldenQ ^ 5 = 5 * goldenQ - 3 := by nlinarith [golden_recurrence 3]
  have h6 : goldenQ ^ 6 = 5 - 8 * goldenQ := by nlinarith [golden_recurrence 4]
  have h7 : goldenQ ^ 7 = 13 * goldenQ - 8 := by nlinarith [golden_recurrence 5]
  have h8 : goldenQ ^ 8 = 13 - 21 * goldenQ := by nlinarith [golden_recurrence 6]
  have h9 : goldenQ ^ 9 = 34 * goldenQ - 21 := by nlinarith [golden_recurrence 7]
  have h10 : goldenQ ^ 10 = 34 - 55 * goldenQ := by nlinarith [golden_recurrence 8]
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem target_active : ScalarEnvelope.ActiveTarget targetT targetA := by
  have hp := golden_properties
  have hg0 : 0 < goldenQ := by linarith [hp.1]
  have h7 := golden_powers.2.2.2.2.2.1
  have h8 := golden_powers.2.2.2.2.2.2.1
  have hrad : 1 - targetT ^ 2 - 2 * targetA = goldenQ ^ 7 := by
    unfold targetT targetA
    rw [show (goldenQ ^ 4) ^ 2 = goldenQ ^ 8 by ring, h7, h8]
    ring
  refine ⟨pow_pos hg0 4, ?_, by unfold targetA; linarith [hp.1], ?_⟩
  · unfold targetT
    nlinarith [hp.2.1, golden_powers.2.2.1]
  · have hpos := pow_pos hg0 7
    linarith

theorem targetX_pos : 0 < targetX := by
  have hp := golden_properties
  unfold targetX
  nlinarith [hp.1, hp.2.2.1]

theorem target_ceiling : ScalarEnvelope.D0 targetT targetA = 4 * (1 - goldenQ) * goldenD := by
  have hp := golden_properties
  have hpow := golden_powers
  have hg0 : 0 < goldenQ := by linarith [hp.1]
  have hw0 : 0 ≤ 1 - goldenQ := by linarith [hp.2.1]
  have hd0 : 0 ≤ goldenD := by unfold goldenD; positivity
  have hroot : Real.sqrt (1 - 2 * targetA) = goldenQ ^ 3 := by
    have heq : 1 - 2 * targetA = (goldenQ ^ 3) ^ 2 := by
      unfold targetA
      rw [show (goldenQ ^ 3) ^ 2 = goldenQ ^ 6 by ring, hpow.2.2.2.2.1]
      ring
    rw [heq, Real.sqrt_sq (by positivity)]
  have hb : ScalarEnvelope.b targetT targetA = 1 - goldenQ := by
    unfold ScalarEnvelope.b targetT targetA
    rw [hpow.2.2.1]
    ring
  have hy : ScalarEnvelope.y0 targetT targetA = goldenQ ^ 5 := by
    unfold ScalarEnvelope.y0 ScalarEnvelope.s targetT
    rw [hroot, hpow.2.1, hpow.2.2.1, hpow.2.2.2.1]
    ring
  have hdsq : goldenD ^ 2 = goldenQ ^ 2 * (1 - goldenQ ^ 2) := by
    unfold goldenD
    rw [mul_pow, Real.sq_sqrt (by nlinarith [hp.2.1])]
  have hrad : (ScalarEnvelope.b targetT targetA) ^ 2 -
      (ScalarEnvelope.y0 targetT targetA) ^ 2 = (2 * (1 - goldenQ) * goldenD) ^ 2 := by
    rw [hb, hy, show (goldenQ ^ 5) ^ 2 = goldenQ ^ 10 by ring, hpow.2.2.2.2.2.2.2.2]
    rw [show (2 * (1 - goldenQ) * goldenD) ^ 2 = 4 * (1 - goldenQ) ^ 2 * goldenD ^ 2 by ring, hdsq]
    ring_nf
    nlinarith [hpow.1, hpow.2.1, hpow.2.2.1, hpow.2.2.2.1, hpow.2.2.2.2.1]
  unfold ScalarEnvelope.D0 ScalarEnvelope.x0
  rw [hrad, Real.sqrt_sq (by positivity)]
  ring

theorem target_ratio : ScalarEnvelope.D0 targetT targetA / targetX = gamma := by
  have hp := golden_properties
  have hg0 : 0 < goldenQ := by linarith [hp.1]
  have hw0 : 0 ≤ 1 - goldenQ := by linarith [hp.2.1]
  have hd0 : 0 ≤ goldenD := by unfold goldenD; positivity
  have h := golden_attained.2.2
  rw [(realMatrix_response hw0 hd0).1, (realMatrix_response hw0 hd0).2] at h
  rwa [target_ceiling] 

theorem unscale_deficit {A C : ℝ} (f : ℕ → ℝ)
    (h : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (A - f m)) atTop (𝓝 C)) :
    Tendsto f atTop (𝓝 A) := by
  have hinv : Tendsto (fun m : ℕ => (1 / (m : ℝ)) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hmul := h.mul hinv
  have hdef : Tendsto (fun m => A - f m) atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun m : ℕ => (m : ℝ) ^ 2 * (A - f m) * (1 / (m : ℝ)) ^ 2) =ᶠ[atTop]
        (fun m => A - f m) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp
    simpa only [mul_zero] using hmul.congr' heq
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A)).sub hdef

def parameters (k P Q M : ℝ) (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hM : 0 < M) :
    PhysicalParameters := ⟨k, P, Q, M, targetT, targetA, hk, hP, hQ, hM, target_active⟩

theorem unit_phase_passive {c rL rR t : ℂ} (hc : Complex.normSq c = 1) (hp : Passive rL rR t) :
    Passive (c * rL) (c * rR) (c * t) := by
  have hc' : c * star c = 1 := by
    have hh := congrArg (fun x : ℝ => (x : ℂ)) hc
    rw [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one] at hh
    simpa only [Complex.star_def, mul_comm] using hh
  have hS : scatteringMatrix (c * rL) (c * rR) (c * t) = c • scatteringMatrix rL rR t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scatteringMatrix]
  change (1 - (scatteringMatrix _ _ _).conjTranspose * scatteringMatrix _ _ _).PosSemidef
  rw [hS]
  unfold Passive absorptionMatrix at hp
  simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hc', one_smul] using hp

theorem unit_phase_response {c : ℂ} (hc : Complex.normSq c = 1) (rL rR t : ℂ) :
    responseAsymmetry (c * rL) (c * rR) (c * t) = responseAsymmetry rL rR t := by
  simp only [responseAsymmetry, absorptanceLeft, absorptanceRight, Complex.normSq_mul, hc, one_mul]

/-- The golden-ratio upper bound applies to the actual physical stack and its
vacuum-normalized reference, after a proved unit-phase normalization of the
entire reciprocal scattering matrix. -/
theorem physical_scalar_upper {k P Q : ℝ} (hk : 0 < k) (layers : List HomogeneousLayer)
    (hadm : StackAdmissible P Q layers) (hX : 0 < stackExtinction k layers) :
    stackAsymmetry k layers / stackExtinction k layers ≤ gamma := by
  let c : ℂ := Complex.exp (-((k * totalThickness layers : ℝ) : ℂ) * Complex.I)
  have hc : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [c, Complex.norm_exp]
  have hp := unit_phase_passive hc (stack_scattering_passive hk hadm)
  have hu := golden_upper (c * stackReflectionLeft k layers) (c * stackReflectionRight k layers)
    (referenceTransmission k layers) hp hX
  change responseAsymmetry (c * stackReflectionLeft k layers) (c * stackReflectionRight k layers)
    (c * stackTransmission k layers) / stackExtinction k layers ≤ gamma at hu
  rw [unit_phase_response hc] at hu
  exact hu

/-- Physical scalar sharpness at the golden target, with the actual
vacuum-reference phase corrected by bounded additional lossless material.
Every physical equality is exact eventually; only the contrast uses a limit. -/
theorem physical_golden_sequence (k P Q M : ℝ) (hk : 0 < k) (hP : 1 < P)
    (hQ : 0 < Q) (hM : 0 < M) :
    ∃ layers : ℕ → List HomogeneousLayer, ∃ C : ℝ,
      (∀ᶠ m : ℕ in atTop, StackAdmissible P Q (layers m) ∧ integratedLoss (layers m) = M ∧
        stackTransmissionPower k (layers m) = targetT ∧ stackMeanAbsorptance k (layers m) = targetA ∧
        referenceTransmission k (layers m) = (goldenQ ^ 2 : ℝ) ∧
        0 < stackExtinction k (layers m) ∧
        k * totalThickness (layers m) ≤ Real.pi * (m : ℝ) / Real.sqrt P + C) ∧
      Tendsto (fun m => stackAsymmetry k (layers m) / stackExtinction k (layers m)) atTop (𝓝 gamma) := by
  let p := parameters k P Q M hk hP hQ hM
  obtain ⟨raw, C, hrawphysical, hrawlimit⟩ := sharp_physical_constructed_sequence p
  obtain ⟨N, hN, hcover⟩ := exists_phase_count hP
  let layers : ℕ → List HomogeneousLayer := fun m => correctedStack k N (raw m)
  have hraw : Tendsto (fun m => stackAsymmetry k (raw m)) atTop
      (𝓝 (ScalarEnvelope.D0 targetT targetA)) := unscale_deficit _ hrawlimit
  have hprops : ∀ᶠ m : ℕ in atTop,
      (StackAdmissible P Q (layers m) ∧ integratedLoss (layers m) = M ∧
        stackTransmissionPower k (layers m) = targetT ∧ stackMeanAbsorptance k (layers m) = targetA ∧
        referenceTransmission k (layers m) = (goldenQ ^ 2 : ℝ) ∧
        0 < stackExtinction k (layers m) ∧
        k * totalThickness (layers m) ≤ Real.pi * (m : ℝ) / Real.sqrt P + (C + periodAngle N)) ∧
      stackAsymmetry k (layers m) = stackAsymmetry k (raw m) ∧
      stackExtinction k (layers m) = targetX := by
    filter_upwards [hrawphysical] with m hm
    have hc := correction_properties hk hP hQ.le hN hcover (raw m) hm.1
    have hT : ‖stackTransmission k (raw m)‖ ^ 2 = goldenQ ^ 4 := by
      have ht := hm.2.2.1
      change transmissionPower (stackTransmission k (raw m)) = targetT at ht
      simpa only [transmissionPower, Complex.normSq_eq_norm_sq, targetT] using ht
    have hnorm : ‖stackTransmission k (raw m)‖ = goldenQ ^ 2 := by
      nlinarith [norm_nonneg (stackTransmission k (raw m)), sq_nonneg goldenQ]
    have href : referenceTransmission k (layers m) = (goldenQ ^ 2 : ℝ) := by
      exact hc.2.2.2.2.2.2.trans (congrArg (fun x : ℝ => (x : ℂ)) hnorm)
    have hX : stackExtinction k (layers m) = targetX := by
      unfold stackExtinction extinction
      rw [href, Complex.ofReal_re]
      rfl
    have hw : k * totalThickness (layers m) ≤ k * totalThickness (raw m) + periodAngle N := by
      calc
        _ ≤ k * (totalThickness (raw m) + periodAngle N / k) :=
          mul_le_mul_of_nonneg_left hc.2.2.2.2.2.1 hk.le
        _ = _ := by field_simp
    refine ⟨⟨hc.1, hc.2.1.trans hm.2.1, hc.2.2.1.trans hm.2.2.1,
      hc.2.2.2.1.trans hm.2.2.2.1, href, by rw [hX]; exact targetX_pos, ?_⟩,
      hc.2.2.2.2.1, hX⟩
    have hrawbound := hm.2.2.2.2
    change k * totalThickness (raw m) ≤ Real.pi * (m : ℝ) / Real.sqrt P + C at hrawbound
    linarith
  refine ⟨layers, C + periodAngle N, hprops.mono (fun _ hm => hm.1), ?_⟩
  have hratio : Tendsto (fun m => stackAsymmetry k (raw m) / targetX) atTop (𝓝 gamma) := by
    simpa only [target_ratio] using hraw.div_const targetX
  apply hratio.congr'
  filter_upwards [hprops] with m hm
  rw [hm.2.1, hm.2.2]

end ScalarPhysicalSharpness
end GeneralizedResearch
