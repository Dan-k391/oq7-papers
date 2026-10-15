import OQ7.Passivity
import GeneralizedResearch.ChannelAttainment
import Mathlib.Tactic

/-! Exact scalar two-port feasibility and its closed-branch sharp envelope.
All realizations are literal complex symmetric scattering matrices with
positive-semidefinite `I - SᴴS`. Material realizability is not asserted here. -/
noncomputable section
namespace GeneralizedResearch
namespace ScalarBenchmark
open OQ7
open scoped Matrix ComplexOrder

def b (T a : ℝ) : ℝ := 1 - T - a
def F (T a x : ℝ) : ℝ := a ^ 2 - x ^ 2 -
  2 * T * (b T a - Real.sqrt ((b T a) ^ 2 - x ^ 2))
def ValidPair (T a : ℝ) : Prop := 0 ≤ T ∧ T ≤ 1 ∧ 0 ≤ a ∧ a ≤ 1 - T
def Feasible (T a δ : ℝ) : Prop :=
  ValidPair T a ∧ |δ| ≤ a ∧ |δ| ≤ b T a ∧ 0 ≤ F T a |δ|
def Realized (T a δ : ℝ) : Prop :=
  ∃ rL rR t : ℂ, Passive rL rR t ∧ transmissionPower t = T ∧
    meanAbsorptance rL rR t = a ∧ halfAsymmetry rL rR t = δ

theorem F_eq_old {T a x : ℝ} (h : 0 ≤ (b T a) ^ 2 - x ^ 2) :
    F T a x = ScalarEnvelope.F T a x := by
  exact (ScalarEnvelope.F_alternative h).symm

theorem passive_feasible (rL rR t : ℂ) (hp : Passive rL rR t) :
    Feasible (transmissionPower t) (meanAbsorptance rL rR t) (halfAsymmetry rL rR t) := by
  obtain ⟨hL, hR⟩ := passive_absorptances_nonneg hp
  have hc := absorptance_coordinates rL rR t
  have hT0 : 0 ≤ transmissionPower t := Complex.normSq_nonneg t
  have hT1 : transmissionPower t ≤ 1 := by
    dsimp [transmissionPower]
    dsimp [absorptanceLeft] at hL
    linarith [Complex.normSq_nonneg rL]
  have ha0 : 0 ≤ meanAbsorptance rL rR t := by
    unfold meanAbsorptance
    linarith
  have ha1 : meanAbsorptance rL rR t ≤ 1 - transmissionPower t := by
    unfold meanAbsorptance absorptanceLeft absorptanceRight transmissionPower
    linarith [Complex.normSq_nonneg rL, Complex.normSq_nonneg rR]
  have hxa : |halfAsymmetry rL rR t| ≤ meanAbsorptance rL rR t := by
    apply abs_le.mpr
    constructor <;> linarith [hc.1, hc.2]
  have hxb := halfAsymmetry_le_b rL rR t
  change |halfAsymmetry rL rR t| ≤ b (transmissionPower t)
    (meanAbsorptance rL rR t) at hxb
  have hb0 : 0 ≤ b (transmissionPower t) (meanAbsorptance rL rR t) := by
    change 0 ≤ ScalarEnvelope.b _ _
    exact (abs_nonneg _).trans hxb
  have hrad : 0 ≤ (b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 -
      |halfAsymmetry rL rR t| ^ 2 := by
    nlinarith [abs_nonneg (halfAsymmetry rL rR t)]
  have hF := (passive_det_nonneg hp).trans (absorption_det_le_envelope rL rR t)
  refine ⟨⟨hT0, hT1, ha0, ha1⟩, hxa, hxb, ?_⟩
  rwa [F_eq_old hrad]

theorem realized_feasible {T a δ : ℝ} (h : Realized T a δ) : Feasible T a δ := by
  obtain ⟨rL, rR, t, hp, ht, ha, hd⟩ := h
  simpa only [ht, ha, hd] using passive_feasible rL rR t hp

/-- Closed two-by-two real PSD criterion, including zero diagonal cases. -/
theorem real_psd_two {l r c : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) (hd : c ^ 2 ≤ l * r) :
    (!![l, c; c, r] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  have hquad (x y : ℝ) : 0 ≤ l * x ^ 2 + 2 * c * x * y + r * y ^ 2 := by
    by_cases hpos : 0 < l
    · have hsum : 0 ≤ l * (l * x ^ 2 + 2 * c * x * y + r * y ^ 2) := by
        calc
          _ ≤ (l * x + c * y) ^ 2 + (l * r - c ^ 2) * y ^ 2 :=
            add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))
          _ = _ := by ring
      exact (mul_le_mul_iff_right₀ hpos).mp (by simpa using hsum)
    · have hz : l = 0 := le_antisymm (le_of_not_gt hpos) hl
      have hc : c = 0 := by nlinarith [sq_nonneg c]
      simpa [hz, hc] using mul_nonneg hr (sq_nonneg y)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro v
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    convert hquad (v 0) (v 1) using 1
    ring

def leftRoot (T a δ : ℝ) : ℝ := Real.sqrt (b T a - δ)
def rightRoot (T a δ : ℝ) : ℝ := Real.sqrt (b T a + δ)
def transRoot (T : ℝ) : ℝ := Real.sqrt T
def optimizerReal (T a δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![leftRoot T a δ, transRoot T; transRoot T, -rightRoot T a δ]
def optimizerLeft (T a δ : ℝ) : ℂ := (leftRoot T a δ : ℂ)
def optimizerRight (T a δ : ℝ) : ℂ := -(rightRoot T a δ : ℂ)
def optimizerTransmission (T : ℝ) : ℂ := (transRoot T : ℂ)
def optimizerOff (T a δ : ℝ) : ℝ :=
  -transRoot T * (leftRoot T a δ - rightRoot T a δ)

theorem feasible_root_properties {T a δ : ℝ} (h : Feasible T a δ) :
    leftRoot T a δ ^ 2 = b T a - δ ∧ rightRoot T a δ ^ 2 = b T a + δ ∧
      transRoot T ^ 2 = T ∧ 0 ≤ a + δ ∧ 0 ≤ a - δ := by
  have hδa := abs_le.mp h.2.1
  have hδb := abs_le.mp h.2.2.1
  exact ⟨Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith),
    Real.sq_sqrt h.1.1, by linarith, by linarith⟩

theorem root_product {T a δ : ℝ} (h : Feasible T a δ) :
    leftRoot T a δ * rightRoot T a δ = Real.sqrt ((b T a) ^ 2 - δ ^ 2) := by
  have hδb := abs_le.mp h.2.2.1
  unfold leftRoot rightRoot
  rw [← Real.sqrt_mul (by linarith : 0 ≤ b T a - δ)]
  congr 1
  ring

theorem optimizerOff_sq {T a δ : ℝ} (h : Feasible T a δ) :
    optimizerOff T a δ ^ 2 = 2 * T *
      (b T a - Real.sqrt ((b T a) ^ 2 - δ ^ 2)) := by
  obtain ⟨hl, hr, ht, _, _⟩ := feasible_root_properties h
  calc
    _ = (transRoot T) ^ 2 * ((leftRoot T a δ) ^ 2 + (rightRoot T a δ) ^ 2 -
      2 * (leftRoot T a δ * rightRoot T a δ)) := by unfold optimizerOff; ring
    _ = _ := by rw [hl, hr, ht, root_product h]; ring

theorem optimizer_defect {T a δ : ℝ} (h : Feasible T a δ) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - (optimizerReal T a δ).transpose * optimizerReal T a δ =
      !![a + δ, optimizerOff T a δ; optimizerOff T a δ, a - δ] := by
  obtain ⟨hl, hr, ht, _, _⟩ := feasible_root_properties h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [optimizerReal, optimizerOff, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals dsimp [b] at hl hr ⊢
  all_goals nlinarith [hl, hr, ht]

theorem optimizer_real_passive {T a δ : ℝ} (h : Feasible T a δ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      (optimizerReal T a δ).transpose * optimizerReal T a δ).PosSemidef := by
  rw [optimizer_defect h]
  have hx := feasible_root_properties h
  apply real_psd_two hx.2.2.2.1 hx.2.2.2.2
  have hF := h.2.2.2
  rw [F, sq_abs, ← optimizerOff_sq h] at hF
  nlinarith

theorem optimizer_matrix (T a δ : ℝ) :
    scatteringMatrix (optimizerLeft T a δ) (optimizerRight T a δ) (optimizerTransmission T) =
      ChannelAttainment.complexify (optimizerReal T a δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scatteringMatrix, optimizerLeft, optimizerRight, optimizerTransmission,
      optimizerReal, ChannelAttainment.complexify]

theorem optimizer_passive {T a δ : ℝ} (h : Feasible T a δ) :
    Passive (optimizerLeft T a δ) (optimizerRight T a δ) (optimizerTransmission T) := by
  change (1 - (scatteringMatrix _ _ _).conjTranspose * scatteringMatrix _ _ _).PosSemidef
  rw [optimizer_matrix]
  exact ChannelAttainment.complexify_contraction _ (optimizer_real_passive h)

theorem optimizer_response {T a δ : ℝ} (h : Feasible T a δ) :
    transmissionPower (optimizerTransmission T) = T ∧
    meanAbsorptance (optimizerLeft T a δ) (optimizerRight T a δ) (optimizerTransmission T) = a ∧
    halfAsymmetry (optimizerLeft T a δ) (optimizerRight T a δ) (optimizerTransmission T) = δ := by
  obtain ⟨hl, hr, ht, _, _⟩ := feasible_root_properties h
  have hL : Complex.normSq (optimizerLeft T a δ) = b T a - δ := by
    simpa only [optimizerLeft, Complex.normSq_ofReal, ← sq] using hl
  have hR : Complex.normSq (optimizerRight T a δ) = b T a + δ := by
    simpa only [optimizerRight, Complex.normSq_neg, Complex.normSq_ofReal, ← sq] using hr
  have hT : Complex.normSq (optimizerTransmission T) = T := by
    simpa only [optimizerTransmission, Complex.normSq_ofReal, ← sq] using ht
  refine ⟨hT, ?_, ?_⟩
  all_goals simp only [meanAbsorptance, halfAsymmetry, absorptanceLeft, absorptanceRight]
  all_goals rw [hL, hR, hT]
  all_goals unfold b; ring

/-- Full feasibility iff for literal complex symmetric contractions. -/
theorem feasibility_iff (T a δ : ℝ) : Realized T a δ ↔ Feasible T a δ := by
  constructor
  · exact realized_feasible
  · intro h
    obtain ⟨ht, ha, hd⟩ := optimizer_response h
    exact ⟨optimizerLeft T a δ, optimizerRight T a δ, optimizerTransmission T,
      optimizer_passive h, ht, ha, hd⟩

def criticalAbsorptance (T : ℝ) : ℝ := (1 - T ^ 2) / 2
def activeGap (T a : ℝ) : ℝ := Real.sqrt (1 - 2 * a) - T
def activeDelta (T a : ℝ) : ℝ :=
  Real.sqrt ((b T a) ^ 2 - (activeGap T a) ^ 2)
def optimalDelta (T a : ℝ) : ℝ :=
  if a < criticalAbsorptance T then activeDelta T a else b T a
def ceiling (T a : ℝ) : ℝ := 2 * optimalDelta T a

theorem b_nonneg {T a : ℝ} (h : ValidPair T a) : 0 ≤ b T a := by
  dsimp [b]
  linarith [h.2.2.2]

theorem active_properties {T a : ℝ} (h : ValidPair T a)
    (ha : a < criticalAbsorptance T) :
    0 < activeGap T a ∧ activeGap T a ≤ b T a ∧
    Real.sqrt (1 - 2 * a) ^ 2 = 1 - 2 * a ∧
    activeDelta T a ^ 2 = (b T a) ^ 2 - (activeGap T a) ^ 2 ∧
    0 ≤ activeDelta T a ∧ activeDelta T a ≤ b T a := by
  have ha0 := h.2.2.1
  have hT0 := h.1
  have hrad : 0 ≤ 1 - 2 * a := by
    dsimp [criticalAbsorptance] at ha
    nlinarith [sq_nonneg T]
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (1 - 2 * a)
  have hsT : T < Real.sqrt (1 - 2 * a) := by
    dsimp [criticalAbsorptance] at ha
    nlinarith
  have hs1 : Real.sqrt (1 - 2 * a) ≤ 1 - a := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith [h.2.2.2], by nlinarith [sq_nonneg a]⟩
  have hg0 : 0 < activeGap T a := by dsimp [activeGap]; linarith
  have hgb : activeGap T a ≤ b T a := by dsimp [activeGap, b]; linarith
  have hb0 := b_nonneg h
  have hdxrad : 0 ≤ (b T a) ^ 2 - (activeGap T a) ^ 2 := by nlinarith
  have hdxsq : activeDelta T a ^ 2 = (b T a) ^ 2 - (activeGap T a) ^ 2 :=
    Real.sq_sqrt hdxrad
  have hdx0 : 0 ≤ activeDelta T a := Real.sqrt_nonneg _
  exact ⟨hg0, hgb, hs, hdxsq, hdx0, by nlinarith [sq_nonneg (activeGap T a)]⟩

theorem active_sqrt_identity {T a : ℝ} (h : ValidPair T a)
    (ha : a < criticalAbsorptance T) :
    Real.sqrt ((b T a) ^ 2 - (activeDelta T a) ^ 2) = activeGap T a := by
  have hp := active_properties h ha
  rw [hp.2.2.2.1]
  have hrad : (b T a) ^ 2 - ((b T a) ^ 2 - (activeGap T a) ^ 2) =
      (activeGap T a) ^ 2 := by ring
  rw [hrad, Real.sqrt_sq (le_of_lt hp.1)]

theorem active_F_zero {T a : ℝ} (h : ValidPair T a)
    (ha : a < criticalAbsorptance T) : F T a (activeDelta T a) = 0 := by
  have hp := active_properties h ha
  dsimp [F]
  rw [active_sqrt_identity h ha, hp.2.2.2.1]
  have hs := hp.2.2.1
  dsimp [activeGap, b] at *
  nlinarith

theorem active_feasible {T a : ℝ} (h : ValidPair T a)
    (ha : a < criticalAbsorptance T) : Feasible T a (activeDelta T a) := by
  have hp := active_properties h ha
  have hF := active_F_zero h ha
  have hda : activeDelta T a ≤ a := by
    have hm := mul_nonneg h.1 (sub_nonneg.mpr hp.2.1)
    dsimp [F] at hF
    rw [active_sqrt_identity h ha] at hF
    nlinarith [h.2.2.1]
  exact ⟨h, by simpa only [abs_of_nonneg hp.2.2.2.2.1] using hda,
    by simpa only [abs_of_nonneg hp.2.2.2.2.1] using hp.2.2.2.2.2,
    by rw [abs_of_nonneg hp.2.2.2.2.1, hF]⟩

theorem active_upper {T a δ : ℝ} (h : Feasible T a δ)
    (ha : a < criticalAbsorptance T) : |δ| ≤ activeDelta T a := by
  have hp := active_properties h.1 ha
  have hb0 := b_nonneg h.1
  have hx0 := abs_nonneg δ
  have hxb := h.2.2.1
  have hrad : 0 ≤ (b T a) ^ 2 - |δ| ^ 2 := by nlinarith
  have hF := h.2.2.2
  rw [F_eq_old hrad, ScalarEnvelope.F] at hF
  change 0 ≤ (Real.sqrt ((b T a) ^ 2 - |δ| ^ 2) + T) ^ 2 - (1 - 2 * a) at hF
  have hradsq := Real.sq_sqrt hrad
  have hroot0 := Real.sqrt_nonneg ((b T a) ^ 2 - |δ| ^ 2)
  have hs0 := Real.sqrt_nonneg (1 - 2 * a)
  have hT0 := h.1.1
  have hs := hp.2.2.1
  have hroot : activeGap T a ≤ Real.sqrt ((b T a) ^ 2 - |δ| ^ 2) := by
    dsimp [activeGap]
    nlinarith
  have hdxsq := hp.2.2.2.1
  have hdx0 := hp.2.2.2.2.1
  have hg0 := hp.1
  nlinarith

theorem plateau_feasible {T a : ℝ} (h : ValidPair T a)
    (ha : criticalAbsorptance T ≤ a) : Feasible T a (b T a) := by
  have hb0 := b_nonneg h
  have hba : b T a ≤ a := by
    have hm := mul_nonneg h.1 (sub_nonneg.mpr h.2.1)
    dsimp [criticalAbsorptance] at ha
    dsimp [b]
    nlinarith
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa only [abs_of_nonneg hb0] using hba
  · simp only [abs_of_nonneg hb0, le_refl]
  · rw [abs_of_nonneg hb0]
    simp only [F, sub_self, Real.sqrt_zero, sub_zero]
    dsimp [criticalAbsorptance] at ha
    dsimp [b]
    nlinarith

theorem optimalDelta_feasible {T a : ℝ} (h : ValidPair T a) :
    Feasible T a (optimalDelta T a) := by
  unfold optimalDelta
  split_ifs with ha
  · exact active_feasible h ha
  · exact plateau_feasible h (le_of_not_gt ha)

theorem feasible_le_optimal {T a δ : ℝ} (h : Feasible T a δ) :
    |δ| ≤ optimalDelta T a := by
  unfold optimalDelta
  split_ifs with ha
  · exact active_upper h ha
  · exact h.2.2.1

theorem optimalDelta_nonneg {T a : ℝ} (h : ValidPair T a) : 0 ≤ optimalDelta T a :=
  (abs_nonneg _).trans (feasible_le_optimal (optimalDelta_feasible h))

theorem F_zero {T a : ℝ} (h : ValidPair T a) : F T a 0 = a ^ 2 := by
  simp only [F, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    Real.sqrt_sq (b_nonneg h), sub_self, mul_zero]

/-- Every allowed mean absorptance is feasible, including degenerate endpoints. -/
theorem zero_feasible {T a : ℝ} (h : ValidPair T a) : Feasible T a 0 := by
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa only [abs_zero] using h.2.2.1
  · simpa only [abs_zero] using b_nonneg h
  · rw [abs_zero, F_zero h]
    exact sq_nonneg _

theorem ceiling_active {T a : ℝ} (ha : a < criticalAbsorptance T) :
    ceiling T a = 2 * Real.sqrt ((1 - T - a) ^ 2 -
      (Real.sqrt (1 - 2 * a) - T) ^ 2) := by
  simp only [ceiling, optimalDelta, ha, ↓reduceIte, activeDelta, activeGap, b]

theorem ceiling_plateau {T a : ℝ} (ha : criticalAbsorptance T ≤ a) :
    ceiling T a = 2 * (1 - T - a) := by
  simp only [ceiling, optimalDelta, not_lt.mpr ha, ↓reduceIte, b]

/-- Both formulas coincide at the transition, including T=0 and T=1. -/
theorem ceiling_transition {T : ℝ} (hT0 : 0 ≤ T) (_hT1 : T ≤ 1) :
    ceiling T (criticalAbsorptance T) = (1 - T) ^ 2 ∧
    2 * Real.sqrt ((b T (criticalAbsorptance T)) ^ 2 -
      (Real.sqrt (1 - 2 * criticalAbsorptance T) - T) ^ 2) = (1 - T) ^ 2 := by
  have hb : b T (criticalAbsorptance T) = (1 - T) ^ 2 / 2 := by
    unfold b criticalAbsorptance
    ring
  have hs : Real.sqrt (1 - 2 * criticalAbsorptance T) = T := by
    have heq : 1 - 2 * criticalAbsorptance T = T ^ 2 := by
      unfold criticalAbsorptance
      ring
    rw [heq, Real.sqrt_sq hT0]
  constructor
  · rw [ceiling_plateau (le_refl _)]
    unfold criticalAbsorptance
    ring
  · rw [hs, sub_self, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
      Real.sqrt_sq (by rw [hb]; positivity), hb]
    ring

theorem ceiling_at_zero_absorptance {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ceiling T 0 = 0 := by
  have hpair : ValidPair T 0 := ⟨hT0, hT1, le_refl _, by linarith⟩
  have hf := optimalDelta_feasible hpair
  have hz : optimalDelta T 0 = 0 := by
    have ha := hf.2.1
    have ho := optimalDelta_nonneg hpair
    rw [abs_of_nonneg ho] at ha
    linarith
  simp only [ceiling, hz, mul_zero]

theorem ceiling_at_unit_transmission {a : ℝ} (h : ValidPair 1 a) : ceiling 1 a = 0 := by
  have ha : a = 0 := by have hh := h.2.2; linarith [hh.1, hh.2]
  rw [ha]
  exact ceiling_at_zero_absorptance (by norm_num) (by norm_num)

theorem passive_ceiling {T a : ℝ} (_h : ValidPair T a) (rL rR t : ℂ)
    (hp : Passive rL rR t) (ht : transmissionPower t = T)
    (ha : meanAbsorptance rL rR t = a) : responseAsymmetry rL rR t ≤ ceiling T a := by
  have hf := passive_feasible rL rR t hp
  rw [ht, ha] at hf
  rw [responseAsymmetry_eq]
  exact mul_le_mul_of_nonneg_left (feasible_le_optimal hf) (by norm_num)

theorem optimizer_attains {T a : ℝ} (h : ValidPair T a) :
    let δ := optimalDelta T a
    Passive (optimizerLeft T a δ) (optimizerRight T a δ) (optimizerTransmission T) ∧
    transmissionPower (optimizerTransmission T) = T ∧
    meanAbsorptance (optimizerLeft T a δ) (optimizerRight T a δ) (optimizerTransmission T) = a ∧
    responseAsymmetry (optimizerLeft T a δ) (optimizerRight T a δ)
      (optimizerTransmission T) = ceiling T a := by
  dsimp only
  have hf := optimalDelta_feasible h
  obtain ⟨ht, ha, hd⟩ := optimizer_response hf
  refine ⟨optimizer_passive hf, ht, ha, ?_⟩
  rw [responseAsymmetry_eq, hd, abs_of_nonneg (optimalDelta_nonneg h)]
  rfl

/-- The full scalar envelope, with an explicit attaining symmetric contraction. -/
theorem sharp_ceiling {T a : ℝ} (h : ValidPair T a) :
    (∀ rL rR t : ℂ, Passive rL rR t → transmissionPower t = T →
      meanAbsorptance rL rR t = a → responseAsymmetry rL rR t ≤ ceiling T a) ∧
    ∃ rL rR t : ℂ, Passive rL rR t ∧ transmissionPower t = T ∧
      meanAbsorptance rL rR t = a ∧ responseAsymmetry rL rR t = ceiling T a := by
  exact ⟨passive_ceiling h, optimizerLeft T a (optimalDelta T a),
    optimizerRight T a (optimalDelta T a), optimizerTransmission T, optimizer_attains h⟩

end ScalarBenchmark
end GeneralizedResearch
