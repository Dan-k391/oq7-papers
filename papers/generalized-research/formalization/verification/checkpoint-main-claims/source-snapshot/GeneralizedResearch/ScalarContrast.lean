import GeneralizedResearch.ScalarBenchmark

/-! Exact fixed-extinction and golden-ratio scalar two-port contrast.
The upper theorem begins with arbitrary complex reciprocal passive amplitudes;
the lower theorem supplies literal amplitudes with a proved PSD defect. -/
noncomputable section
namespace GeneralizedResearch
namespace ScalarContrast
open OQ7
open scoped Matrix ComplexOrder

def extinction (t : ℂ) : ℝ := 2 * (1 - t.re)
def phaseReduced (rL rR t : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![‖rL‖, ‖t‖; ‖t‖, -‖rR‖]
def w (rL rR : ℂ) : ℝ := |‖rL‖ - ‖rR‖| / 2
def d (rL rR : ℂ) : ℝ := (‖rL‖ + ‖rR‖) / 2
def q (rL rR t : ℂ) : ℝ := Real.sqrt (d rL rR ^ 2 + ‖t‖ ^ 2)

theorem phase_reduced_passive (rL rR t : ℂ) (hp : Passive rL rR t) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      (phaseReduced rL rR t).transpose * phaseReduced rL rR t).PosSemidef := by
  have hf := ScalarBenchmark.passive_feasible rL rR t hp
  obtain ⟨hl, hr, ht, _, _⟩ := ScalarBenchmark.feasible_root_properties hf
  have hc := reflection_coordinates rL rR t
  have hcL := hc.1
  have hcR := hc.2
  have hl' : ScalarBenchmark.leftRoot (transmissionPower t)
      (meanAbsorptance rL rR t) (halfAsymmetry rL rR t) = ‖rL‖ := by
    change _ = ScalarBenchmark.b _ _ - _ at hl
    change Complex.normSq rL = ScalarBenchmark.b _ _ - _ at hcL
    have hroot : 0 ≤ ScalarBenchmark.leftRoot (transmissionPower t)
      (meanAbsorptance rL rR t) (halfAsymmetry rL rR t) := Real.sqrt_nonneg _
    nlinarith [Complex.normSq_eq_norm_sq rL, norm_nonneg rL]
  have hr' : ScalarBenchmark.rightRoot (transmissionPower t)
      (meanAbsorptance rL rR t) (halfAsymmetry rL rR t) = ‖rR‖ := by
    change _ = ScalarBenchmark.b _ _ + _ at hr
    change Complex.normSq rR = ScalarBenchmark.b _ _ + _ at hcR
    have hroot : 0 ≤ ScalarBenchmark.rightRoot (transmissionPower t)
      (meanAbsorptance rL rR t) (halfAsymmetry rL rR t) := Real.sqrt_nonneg _
    nlinarith [Complex.normSq_eq_norm_sq rR, norm_nonneg rR]
  have ht' : ScalarBenchmark.transRoot (transmissionPower t) = ‖t‖ := by
    change _ = Complex.normSq t at ht
    have hroot : 0 ≤ ScalarBenchmark.transRoot (transmissionPower t) := Real.sqrt_nonneg _
    nlinarith [Complex.normSq_eq_norm_sq t, norm_nonneg t]
  have heq : ScalarBenchmark.optimizerReal (transmissionPower t)
      (meanAbsorptance rL rR t) (halfAsymmetry rL rR t) = phaseReduced rL rR t := by
    simp only [ScalarBenchmark.optimizerReal, phaseReduced, hl', hr', ht']
  rw [← heq]
  exact ScalarBenchmark.optimizer_real_passive hf

theorem parameter_identities (rL rR t : ℂ) :
    0 ≤ w rL rR ∧ 0 ≤ d rL rR ∧ 0 ≤ q rL rR t ∧
    w rL rR ^ 2 + d rL rR ^ 2 = (‖rL‖ ^ 2 + ‖rR‖ ^ 2) / 2 ∧
    q rL rR t ^ 2 = d rL rR ^ 2 + ‖t‖ ^ 2 ∧
    responseAsymmetry rL rR t = 4 * w rL rR * d rL rR := by
  have hw0 : 0 ≤ w rL rR := div_nonneg (abs_nonneg _) (by norm_num)
  have hd0 : 0 ≤ d rL rR := by unfold d; positivity
  have hq0 : 0 ≤ q rL rR t := Real.sqrt_nonneg _
  have hq : q rL rR t ^ 2 = d rL rR ^ 2 + ‖t‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hwd : w rL rR ^ 2 + d rL rR ^ 2 = (‖rL‖ ^ 2 + ‖rR‖ ^ 2) / 2 := by
    unfold w d
    rw [div_pow, sq_abs]
    ring
  refine ⟨hw0, hd0, hq0, hwd, hq, ?_⟩
  unfold responseAsymmetry absorptanceLeft absorptanceRight
  rw [Complex.normSq_eq_norm_sq rL, Complex.normSq_eq_norm_sq rR]
  have heq : (1 - ‖rL‖ ^ 2 - Complex.normSq t) -
      (1 - ‖rR‖ ^ 2 - Complex.normSq t) = -(‖rL‖ - ‖rR‖) * (‖rL‖ + ‖rR‖) := by ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ‖rL‖ + ‖rR‖)]
  unfold w d
  ring

theorem passive_parameters (rL rR t : ℂ) (hp : Passive rL rR t) :
    w rL rR + q rL rR t ≤ 1 := by
  have hred := phase_reduced_passive rL rR t hp
  have h0 := hred.diag_nonneg (i := 0)
  have h1 := hred.diag_nonneg (i := 1)
  have hdet := hred.det_nonneg
  simp [phaseReduced, Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
  simp [phaseReduced, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at hdet
  obtain ⟨hw0, hd0, hq0, hwd, hq, _⟩ := parameter_identities rL rR t
  have hw2 : w rL rR ^ 2 = (‖rL‖ - ‖rR‖) ^ 2 / 4 := by
    unfold w
    rw [div_pow, sq_abs]
    norm_num
  have hc0 : 0 ≤ 1 - w rL rR ^ 2 - q rL rR t ^ 2 := by nlinarith
  have hdet' : 0 ≤ (1 - w rL rR ^ 2 - q rL rR t ^ 2) ^ 2 -
      (2 * w rL rR * q rL rR t) ^ 2 := by
    calc
      _ ≤ (1 - ‖rL‖ ^ 2 - ‖t‖ ^ 2) * (1 - ‖rR‖ ^ 2 - ‖t‖ ^ 2) -
          (‖t‖ * (‖rL‖ - ‖rR‖)) ^ 2 := by nlinarith [hdet]
      _ = _ := by
        rw [show (2 * w rL rR * q rL rR t) ^ 2 =
          4 * w rL rR ^ 2 * q rL rR t ^ 2 by ring, hq, hw2]
        unfold d
        ring
  have hwq0 : 0 ≤ 2 * w rL rR * q rL rR t := by positivity
  have hc : 2 * w rL rR * q rL rR t ≤ 1 - w rL rR ^ 2 - q rL rR t ^ 2 := by
    nlinarith
  nlinarith

def realMatrix (w d c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![w + d, c; c, w - d]
def left (w d : ℝ) : ℂ := ((w + d : ℝ) : ℂ)
def right (w d : ℝ) : ℂ := ((w - d : ℝ) : ℂ)
def trans (c : ℝ) : ℂ := (c : ℂ)

theorem realMatrix_passive {w d c q : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d)
    (hq : 0 ≤ q) (hsq : d ^ 2 + c ^ 2 = q ^ 2) (hbound : w + q ≤ 1) :
    Passive (left w d) (right w d) (trans c) := by
  have hq1 : q ≤ 1 := by linarith
  have hdq : d ≤ q := by nlinarith [sq_nonneg c]
  have hplus : 0 ≤ 1 - (w + q) ^ 2 := by nlinarith
  have hminus : 0 ≤ 1 - (w - q) ^ 2 := by nlinarith
  have hdef : ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      (realMatrix w d c).transpose * realMatrix w d c).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℝ) -
        (realMatrix w d c).transpose * realMatrix w d c =
        !![1 - (w + d) ^ 2 - c ^ 2, -2 * w * c;
          -2 * w * c, 1 - (w - d) ^ 2 - c ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [realMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [heq]
    apply ScalarBenchmark.real_psd_two
    · nlinarith [mul_nonneg hw (sub_nonneg.mpr hdq)]
    · nlinarith [mul_nonneg hw (add_nonneg hd hq)]
    · have hprod := mul_nonneg hplus hminus
      nlinarith [hsq]
  change (1 - (scatteringMatrix _ _ _).conjTranspose * scatteringMatrix _ _ _).PosSemidef
  have heq : scatteringMatrix (left w d) (right w d) (trans c) =
      ChannelAttainment.complexify (realMatrix w d c) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scatteringMatrix, left, right, trans, ChannelAttainment.complexify, realMatrix]
  rw [heq]
  exact ChannelAttainment.complexify_contraction _ hdef

theorem realMatrix_response {w d c : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    extinction (trans c) = 2 * (1 - c) ∧
      responseAsymmetry (left w d) (right w d) (trans c) = 4 * w * d := by
  constructor
  · simp [extinction, trans]
  · unfold responseAsymmetry absorptanceLeft absorptanceRight left right trans
    simp only [Complex.normSq_ofReal]
    have heq : (1 - (w + d) * (w + d) - c * c) -
        (1 - (w - d) * (w - d) - c * c) = -(4 * w * d) := by ring
    rw [heq, abs_neg, abs_of_nonneg (by positivity)]

def fixedQ (c : ℝ) : ℝ := (1 + Real.sqrt (1 + 8 * c ^ 2)) / 4
def fixedD (c : ℝ) : ℝ := Real.sqrt (fixedQ c * (1 - fixedQ c))
def fixedCeiling (X : ℝ) : ℝ := 4 * (1 - fixedQ (1 - X / 2)) * fixedD (1 - X / 2)

theorem fixedQ_properties {c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    (1 / 2 : ℝ) ≤ fixedQ c ∧ fixedQ c ≤ 1 ∧
    2 * fixedQ c ^ 2 - fixedQ c - c ^ 2 = 0 ∧
    fixedD c ^ 2 + c ^ 2 = fixedQ c ^ 2 ∧ 0 ≤ fixedD c := by
  have hr : 0 ≤ 1 + 8 * c ^ 2 := by positivity
  have hs := Real.sq_sqrt hr
  have hs0 := Real.sqrt_nonneg (1 + 8 * c ^ 2)
  have hs1 : 1 ≤ Real.sqrt (1 + 8 * c ^ 2) := by nlinarith [sq_nonneg c]
  have hs3 : Real.sqrt (1 + 8 * c ^ 2) ≤ 3 := by nlinarith
  have hp0 : (1 / 2 : ℝ) ≤ fixedQ c := by unfold fixedQ; linarith
  have hp1 : fixedQ c ≤ 1 := by unfold fixedQ; linarith
  have hpeq : 2 * fixedQ c ^ 2 - fixedQ c - c ^ 2 = 0 := by unfold fixedQ; nlinarith
  have hdp : fixedD c ^ 2 = fixedQ c * (1 - fixedQ c) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  exact ⟨hp0, hp1, hpeq, by nlinarith, Real.sqrt_nonneg _⟩

/-- The exact fixed-extinction quartic optimizer, proved by a nonnegative
polynomial remainder rather than a numerical optimization. -/
theorem fixed_polynomial_maximum {p q c : ℝ} (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heq : 2 * p ^ 2 - p - c ^ 2 = 0) :
    (1 - q) ^ 2 * (q ^ 2 - c ^ 2) ≤ (1 - p) ^ 2 * p * (1 - p) := by
  have hB : 0 ≤ p * (1 - p) + (1 - q) * (2 * p - 1 + q) := by
    exact add_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  have hprod := mul_nonneg (sq_nonneg (q - p)) hB
  have hid : (1 - p) ^ 2 * p * (1 - p) - (1 - q) ^ 2 * (q ^ 2 - c ^ 2) =
      (q - p) ^ 2 * (p * (1 - p) + (1 - q) * (2 * p - 1 + q)) := by
    have hc : c ^ 2 = 2 * p ^ 2 - p := by linarith
    rw [hc]
    ring
  linarith

theorem fixed_parameter_upper {w d q σ c : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d)
    (hq : 0 ≤ q) (hbound : w + q ≤ 1) (hsq : d ^ 2 + σ ^ 2 = q ^ 2)
    (hc : c ^ 2 ≤ σ ^ 2) (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    4 * w * d ≤ 4 * (1 - fixedQ c) * fixedD c := by
  have hq1 : q ≤ 1 := by linarith
  have hp := fixedQ_properties hc0 hc1
  have hopt := fixed_polynomial_maximum hp.1 hp.2.1 hq hq1 hp.2.2.1
  have hdsq : d ^ 2 ≤ q ^ 2 - c ^ 2 := by linarith
  have hB : (4 * (1 - q) * d) ^ 2 ≤
      16 * ((1 - q) ^ 2 * (q ^ 2 - c ^ 2)) := by
    calc
      _ = (16 * (1 - q) ^ 2) * d ^ 2 := by ring
      _ ≤ (16 * (1 - q) ^ 2) * (q ^ 2 - c ^ 2) :=
        mul_le_mul_of_nonneg_left hdsq (by positivity)
      _ = _ := by ring
  have hDsq : (4 * (1 - fixedQ c) * fixedD c) ^ 2 =
      16 * ((1 - fixedQ c) ^ 2 * fixedQ c * (1 - fixedQ c)) := by
    have hh : fixedD c ^ 2 = fixedQ c * (1 - fixedQ c) := by
      nlinarith [hp.2.2.1, hp.2.2.2.1]
    calc
      _ = 16 * (1 - fixedQ c) ^ 2 * fixedD c ^ 2 := by ring
      _ = _ := by rw [hh]; ring
  have hopt' := mul_le_mul_of_nonneg_left hopt (by norm_num : (0 : ℝ) ≤ 16)
  have hB0 : 0 ≤ 4 * (1 - q) * d := by positivity
  have hD0 : 0 ≤ 4 * (1 - fixedQ c) * fixedD c := by
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [hp.2.1])) hp.2.2.2.2
  have hle : 4 * (1 - q) * d ≤ 4 * (1 - fixedQ c) * fixedD c := by nlinarith
  have hwd : 4 * w * d ≤ 4 * (1 - q) * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : w ≤ 1 - q)) hd]
  exact hwd.trans hle

theorem fixed_extinction_upper (rL rR t : ℂ) (hp : Passive rL rR t) :
    responseAsymmetry rL rR t ≤ fixedCeiling (extinction t) := by
  obtain ⟨hw0, hd0, hq0, _, hsq, hresponse⟩ := parameter_identities rL rR t
  have hbound := passive_parameters rL rR t hp
  have hnorm : ‖t‖ ≤ 1 := by
    have h := passive_absorptances_nonneg hp
    have hL := h.1
    unfold absorptanceLeft at hL
    rw [Complex.normSq_eq_norm_sq t, Complex.normSq_eq_norm_sq rL] at hL
    nlinarith [norm_nonneg t, sq_nonneg ‖rL‖]
  have hre := abs_le.mp ((Complex.abs_re_le_norm t).trans hnorm)
  have hre2 : t.re ^ 2 ≤ ‖t‖ ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_norm] using Complex.abs_re_le_norm t)
  have h := fixed_parameter_upper hw0 hd0 hq0 hbound hsq.symm hre2 hre.1 hre.2
  rw [hresponse]
  have heq : 1 - extinction t / 2 = t.re := by unfold extinction; ring
  simpa only [fixedCeiling, heq] using h

theorem fixed_ceiling_attained {X : ℝ} (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    let c := 1 - X / 2
    let p := fixedQ c
    Passive (left (1 - p) (fixedD c)) (right (1 - p) (fixedD c)) (trans c) ∧
    extinction (trans c) = X ∧
    responseAsymmetry (left (1 - p) (fixedD c)) (right (1 - p) (fixedD c))
      (trans c) = fixedCeiling X := by
  dsimp only
  have hc0 : -1 ≤ 1 - X / 2 := by linarith
  have hc1 : 1 - X / 2 ≤ 1 := by linarith
  have hp := fixedQ_properties hc0 hc1
  have hw : 0 ≤ 1 - fixedQ (1 - X / 2) := by linarith [hp.2.1]
  refine ⟨realMatrix_passive hw hp.2.2.2.2 (by linarith [hp.1]) hp.2.2.2.1 (by linarith), ?_, ?_⟩
  · rw [(realMatrix_response hw hp.2.2.2.2).1]
    ring
  · exact (realMatrix_response hw hp.2.2.2.2).2

/-- The exact original equation (50), as a universal upper bound and a literal
attaining reciprocal passive two-port, for every closed endpoint 0≤X≤4. -/
theorem fixed_extinction_sharp {X : ℝ} (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    (∀ rL rR t : ℂ, Passive rL rR t → extinction t = X →
      responseAsymmetry rL rR t ≤ fixedCeiling X) ∧
    ∃ rL rR t : ℂ, Passive rL rR t ∧ extinction t = X ∧
      responseAsymmetry rL rR t = fixedCeiling X := by
  constructor
  · intro rL rR t hp hX
    simpa only [hX] using fixed_extinction_upper rL rR t hp
  · exact ⟨left (1 - fixedQ (1 - X / 2)) (fixedD (1 - X / 2)),
      right (1 - fixedQ (1 - X / 2)) (fixedD (1 - X / 2)), trans (1 - X / 2),
      fixed_ceiling_attained hX0 hX4⟩

theorem fixed_ceiling_symmetry (X : ℝ) : fixedCeiling (4 - X) = fixedCeiling X := by
  have heq : 1 - (4 - X) / 2 = -(1 - X / 2) := by ring
  simp only [fixedCeiling, heq, fixedD, fixedQ, neg_sq]

theorem fixed_ceiling_endpoints : fixedCeiling 0 = 0 ∧ fixedCeiling 4 = 0 := by
  norm_num [fixedCeiling, fixedD, fixedQ]

/-- Literal radical/power form of original equation (50). -/
theorem fixed_ceiling_formula {X : ℝ} (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    let τ := |1 - X / 2|
    let p := (1 + Real.sqrt (1 + 8 * τ ^ 2)) / 4
    fixedCeiling X = 4 * Real.sqrt p * (1 - p) ^ (3 / 2 : ℝ) := by
  dsimp only
  rw [sq_abs]
  change fixedCeiling X = 4 * Real.sqrt (fixedQ (1 - X / 2)) *
    (1 - fixedQ (1 - X / 2)) ^ (3 / 2 : ℝ)
  have hp := fixedQ_properties (by linarith : -1 ≤ 1 - X / 2) (by linarith : 1 - X / 2 ≤ 1)
  by_cases heq : fixedQ (1 - X / 2) = 1
  · norm_num [fixedCeiling, fixedD, heq]
  · have hb : 0 < 1 - fixedQ (1 - X / 2) := by
      by_contra hh
      exact heq (by linarith [hp.2.1, le_of_not_gt hh])
    rw [fixedCeiling, fixedD, Real.sqrt_mul (by linarith [hp.1]),
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hb, Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring

def goldenQ : ℝ := (Real.sqrt 5 - 1) / 2
def gamma : ℝ := Real.sqrt (10 * Real.sqrt 5 - 22)
def goldenD : ℝ := goldenQ * Real.sqrt (1 - goldenQ ^ 2)

theorem golden_properties : (1 / 2 : ℝ) < goldenQ ∧ goldenQ < 1 ∧
    goldenQ ^ 2 + goldenQ = 1 ∧ 0 < gamma ∧ gamma ^ 2 = 20 * goldenQ - 12 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs2 : (2 : ℝ) < Real.sqrt 5 := by nlinarith
  have hs3 : Real.sqrt 5 < (3 : ℝ) := by nlinarith
  have hrad : 0 < 10 * Real.sqrt 5 - 22 := by nlinarith
  refine ⟨?_, ?_, ?_, Real.sqrt_pos.mpr hrad, ?_⟩
  · unfold goldenQ
    linarith
  · unfold goldenQ
    linarith
  · unfold goldenQ
    nlinarith
  · unfold gamma goldenQ
    rw [Real.sq_sqrt hrad.le]
    ring

/-- Exact global golden-ratio certificate for the remaining scalar variable. -/
theorem golden_polynomial_maximum {q : ℝ} (hq : 0 ≤ q) :
    4 * q ^ 2 * (1 - q) ≤ gamma ^ 2 * (1 + q) := by
  have hp := golden_properties
  have hprod : 0 ≤ 4 * (q - goldenQ) ^ 2 * (q + 2 * goldenQ - 1) := by
    exact mul_nonneg (by positivity) (by linarith [hp.1])
  have hid : gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q) =
      4 * (q - goldenQ) ^ 2 * (q + 2 * goldenQ - 1) := by
    rw [hp.2.2.2.2]
    linear_combination (4 * (3 + 3 * q - 2 * goldenQ)) * hp.2.2.1
  linarith

theorem golden_parameter_upper {w d q σ : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d)
    (hq : 0 ≤ q) (_hσ : 0 ≤ σ) (hbound : w + q ≤ 1)
    (hsq : d ^ 2 + σ ^ 2 = q ^ 2) : 4 * w * d ≤ 2 * gamma * (1 - σ) := by
  have hq1 : q ≤ 1 := by linarith
  have hσq : σ ≤ q := by nlinarith [sq_nonneg d]
  have hσ1 : σ ≤ 1 := hσq.trans hq1
  have hg := golden_polynomial_maximum hq
  have hfirst := mul_nonneg (sub_nonneg.mpr hg) (sq_nonneg (1 - σ))
  have hsecond : 0 ≤ 4 * (1 - q) * (σ - q ^ 2) ^ 2 := by positivity
  have hid : (1 + q) * (gamma ^ 2 * (1 - σ) ^ 2 - 4 * (1 - q) ^ 2 * d ^ 2) =
      (gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q)) * (1 - σ) ^ 2 +
        4 * (1 - q) * (σ - q ^ 2) ^ 2 := by
    linear_combination -(4 * (1 - q) ^ 2 * (1 + q)) * hsq
  have hsqbound : 0 ≤ gamma ^ 2 * (1 - σ) ^ 2 - 4 * (1 - q) ^ 2 * d ^ 2 := by
    have hsum : 0 ≤ (1 + q) *
        (gamma ^ 2 * (1 - σ) ^ 2 - 4 * (1 - q) ^ 2 * d ^ 2) := by
      rw [hid]
      exact add_nonneg hfirst hsecond
    exact (mul_nonneg_iff_of_pos_left (by linarith : 0 < 1 + q)).mp hsum
  have hleft0 : 0 ≤ 2 * (1 - q) * d := by positivity
  have hright0 : 0 ≤ gamma * (1 - σ) :=
    mul_nonneg (le_of_lt golden_properties.2.2.2.1) (by linarith)
  have hle : 2 * (1 - q) * d ≤ gamma * (1 - σ) := by
    apply (sq_le_sq₀ hleft0 hright0).mp
    nlinarith [hsqbound]
  have hwd : 4 * w * d ≤ 4 * (1 - q) * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : w ≤ 1 - q)) hd]
  linarith

theorem golden_upper (rL rR t : ℂ) (hp : Passive rL rR t) (hX : 0 < extinction t) :
    responseAsymmetry rL rR t / extinction t ≤ gamma := by
  obtain ⟨hw0, hd0, hq0, _, hsq, hresponse⟩ := parameter_identities rL rR t
  have hbound := passive_parameters rL rR t hp
  have h := golden_parameter_upper hw0 hd0 hq0 (norm_nonneg t) hbound hsq.symm
  have hre : t.re ≤ ‖t‖ := (le_abs_self _).trans (Complex.abs_re_le_norm t)
  have hg0 := le_of_lt golden_properties.2.2.2.1
  apply (div_le_iff₀ hX).mpr
  rw [hresponse]
  have hnorm := mul_le_mul_of_nonneg_left (sub_le_sub_left hre 1) hg0
  unfold extinction
  nlinarith

theorem golden_attained :
    Passive (left (1 - goldenQ) goldenD) (right (1 - goldenQ) goldenD) (trans (goldenQ ^ 2)) ∧
    0 < extinction (trans (goldenQ ^ 2)) ∧
    responseAsymmetry (left (1 - goldenQ) goldenD) (right (1 - goldenQ) goldenD)
      (trans (goldenQ ^ 2)) / extinction (trans (goldenQ ^ 2)) = gamma := by
  have hp := golden_properties
  have hg0 : 0 < goldenQ := by linarith [hp.1]
  have hw0 : 0 ≤ 1 - goldenQ := by linarith [hp.2.1]
  have hrad : 0 ≤ 1 - goldenQ ^ 2 := by nlinarith [hp.2.1]
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (1 - goldenQ ^ 2)
  have hd0 : 0 ≤ goldenD := mul_nonneg hg0.le hs0
  have hdsq : goldenD ^ 2 + (goldenQ ^ 2) ^ 2 = goldenQ ^ 2 := by
    unfold goldenD
    rw [mul_pow, hs]
    ring
  have hpass := realMatrix_passive hw0 hd0 hg0.le hdsq (by linarith)
  have hX : extinction (trans (goldenQ ^ 2)) = 2 * goldenQ := by
    rw [(realMatrix_response hw0 hd0).1]
    linarith [hp.2.2.1]
  refine ⟨hpass, by rw [hX]; positivity, ?_⟩
  have hg3 : goldenQ ^ 3 = 2 * goldenQ - 1 := by
    nlinarith [hp.2.2.1]
  have hgam : gamma = 2 * (1 - goldenQ) * Real.sqrt (1 - goldenQ ^ 2) := by
    apply (sq_eq_sq₀ (le_of_lt hp.2.2.2.1) (by positivity)).mp
    rw [mul_pow, mul_pow, hs, hp.2.2.2.2]
    nlinarith [hp.2.2.1, hg3]
  rw [(realMatrix_response hw0 hd0).2, hX, hgam]
  unfold goldenD
  field_simp [hg0.ne']
  ring

/-- Full original Theorem 6.3 inequality and exact equality construction.
Classification of every attaining phase and scalar dielectric approach are
separate assertions and are not encoded in this theorem. -/
theorem theorem63 :
    (∀ rL rR t : ℂ, Passive rL rR t → 0 < extinction t →
      responseAsymmetry rL rR t / extinction t ≤ gamma) ∧
    ∃ rL rR t : ℂ, Passive rL rR t ∧ 0 < extinction t ∧
      responseAsymmetry rL rR t / extinction t = gamma :=
  ⟨golden_upper, left (1 - goldenQ) goldenD, right (1 - goldenQ) goldenD,
    trans (goldenQ ^ 2), golden_attained⟩

end ScalarContrast
end GeneralizedResearch
