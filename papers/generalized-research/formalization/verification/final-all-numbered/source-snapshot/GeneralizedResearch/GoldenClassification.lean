import GeneralizedResearch.ScalarContrast
import GeneralizedResearch.ScalarPhaseFeasibility
import GeneralizedResearch.ScalarGoldenParameters
import GeneralizedResearch.ScalarPhaseSymmetry

/-! Literal all-equality-matrix phase family in original Theorem 6.3. -/
noncomputable section
set_option maxHeartbeats 3000000
namespace GeneralizedResearch.GoldenClassification
open OQ7 ScalarContrast
open scoped Matrix ComplexOrder

theorem saturated_reflection_product {rL rR : ℂ} {w d c q : ℝ}
    (hp : Passive rL rR (c : ℂ)) (hc : 0 < c)
    (hL : ‖rL‖ = w + d) (hR : ‖rR‖ = d - w)
    (hbound : w + q = 1) (hsq : d ^ 2 + c ^ 2 = q ^ 2) :
    rL * rR = ((w ^ 2 - d ^ 2 : ℝ) : ℂ) := by
  have hnsL : Complex.normSq rL = (w + d) ^ 2 := by rw [Complex.normSq_eq_norm_sq, hL]
  have hnsR : Complex.normSq rR = (d - w) ^ 2 := by rw [Complex.normSq_eq_norm_sq, hR]
  have hdet := passive_det_nonneg hp
  rw [absorption_det, Complex.ofReal_re,
    ScalarPhaseFeasibility.normSq_interference] at hdet
  have hphase : (rL * rR * (star (c : ℂ)) ^ 2).re = (rL * rR).re * c ^ 2 := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hphase, hnsL, hnsR] at hdet
  simp only [absorptanceLeft, absorptanceRight, Complex.normSq_ofReal,
    transmissionPower] at hdet
  rw [hnsL, hnsR] at hdet
  have hid : (1 - (w + d) ^ 2 - c * c) * (1 - (d - w) ^ 2 - c * c) -
      ((c * c) * ((w + d) ^ 2 + (d - w) ^ 2) + 2 * ((rL * rR).re * c ^ 2)) =
      -2 * c ^ 2 * (d ^ 2 - w ^ 2 + (rL * rR).re) := by
    have hw : w = 1 - q := by linarith
    rw [hw]
    linear_combination (d ^ 2 + c ^ 2 - q ^ 2 + 4 * q - 4) * hsq
  rw [hid] at hdet
  have hreal : d ^ 2 - w ^ 2 + (rL * rR).re ≤ 0 := by
    nlinarith only [hdet, sq_pos_of_pos hc]
  have ha : 0 ≤ d ^ 2 - w ^ 2 := by
    have hh := mul_nonneg (norm_nonneg rL) (norm_nonneg rR)
    rw [hL,hR] at hh
    nlinarith only [hh]
  have hnprod : Complex.normSq (rL * rR) = (d ^ 2 - w ^ 2) ^ 2 := by
    rw [Complex.normSq_mul,hnsL,hnsR]
    ring
  have hnadd : Complex.normSq (rL * rR + ((d ^ 2 - w ^ 2 : ℝ) : ℂ)) =
      2 * (d ^ 2 - w ^ 2) * (d ^ 2 - w ^ 2 + (rL * rR).re) := by
    rw [Complex.normSq_add,hnprod]
    simp only [Complex.normSq_ofReal, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hz : rL * rR + ((d ^ 2 - w ^ 2 : ℝ) : ℂ) = 0 := by
    apply Complex.normSq_eq_zero.mp
    have hn := Complex.normSq_nonneg (rL * rR + ((d ^ 2 - w ^ 2 : ℝ) : ℂ))
    rw [hnadd] at hn ⊢
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hreal]
  have hcst : ((w ^ 2 - d ^ 2 : ℝ) : ℂ) = -((d ^ 2 - w ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcst]
  exact eq_neg_of_add_eq_zero_left hz

theorem phase_from_product {rL rR : ℂ} {A B : ℝ}
    (hA : 0 < A) (hL : ‖rL‖ = A) (hprod : rL * rR = ((A * B : ℝ) : ℂ)) :
    ∃ φ : ℝ, rL = (A : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∧
      rR = (B : ℂ) * Complex.exp ((-φ : ℂ) * Complex.I) := by
  have hne : rL ≠ 0 := norm_pos_iff.mp (by rwa [hL])
  have harg : rL = (A : ℂ) * Complex.exp ((rL.arg : ℂ) * Complex.I) := by
    rw [←hL]
    exact (Complex.norm_mul_exp_arg_mul_I rL).symm
  refine ⟨rL.arg,harg,?_⟩
  apply mul_left_cancel₀ hne
  rw [hprod]
  nth_rw 1 [harg]
  have hexp : Complex.exp ((rL.arg : ℂ) * Complex.I) *
      Complex.exp ((-rL.arg : ℂ) * Complex.I) = 1 := by
    rw [←Complex.exp_add]
    have hz : (rL.arg : ℂ) * Complex.I + (-rL.arg : ℂ) * Complex.I = 0 := by
      ring
    rw [hz,Complex.exp_zero]
  push_cast
  calc
    (A : ℂ) * B = (A : ℂ) * B * 1 := by ring
    _ = (A : ℂ) * B *
        (Complex.exp ((rL.arg : ℂ) * Complex.I) *
          Complex.exp ((-rL.arg : ℂ) * Complex.I)) := by rw [hexp]
    _ = _ := by ring

theorem equality_magnitudes {rL rR t : ℂ} (hp : Passive rL rR t)
    (hX : 0 < extinction t)
    (heq : responseAsymmetry rL rR t / extinction t = gamma) :
    t = ((goldenQ ^ 2 : ℝ) : ℂ) ∧ w rL rR = 1 - goldenQ ∧
      d rL rR = goldenD ∧ q rL rR t = goldenQ := by
  obtain ⟨hw,hd,hq,_,hsq,hresponse⟩ := parameter_identities rL rR t
  have hbound := passive_parameters rL rR t hp
  have hg : 0 < gamma := golden_properties.2.2.2.1
  have hparam := golden_parameter_upper hw hd hq (norm_nonneg t) hbound hsq.symm
  have hD : responseAsymmetry rL rR t = gamma * extinction t :=
    (div_eq_iff (ne_of_gt hX)).mp heq
  have hre : t.re ≤ ‖t‖ := (le_abs_self _).trans (Complex.abs_re_le_norm t)
  have hreal : t.re = ‖t‖ := by
    rw [hresponse] at hD
    unfold extinction at hD
    nlinarith only [hD,hparam,hre,hg]
  have hσ : ‖t‖ < 1 := by unfold extinction at hX; linarith only [hX,hreal]
  have hpe : 4 * w rL rR * d rL rR = 2 * gamma * (1 - ‖t‖) := by
    rw [hresponse] at hD
    unfold extinction at hD
    rw [hreal] at hD
    linarith only [hD]
  have hpars := ScalarGoldenParameters.equality_parameters hw hd hq
    (norm_nonneg t) hσ hbound hsq.symm hpe
  have him : t.im = 0 := Complex.abs_re_eq_norm.mp (by rw [hreal]; exact abs_of_nonneg (norm_nonneg t))
  refine ⟨?_,hpars.2.1,hpars.2.2.2,hpars.1⟩
  apply Complex.ext
  · simpa only [Complex.ofReal_re,hpars.2.2.1] using hreal
  · simpa only [Complex.ofReal_im] using him

def familyLeft (φ : ℝ) : ℂ :=
  ((1 - goldenQ + goldenD : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
def familyRight (φ : ℝ) : ℂ :=
  ((1 - goldenQ - goldenD : ℝ) : ℂ) * Complex.exp ((-φ : ℂ) * Complex.I)
def familyTransmission : ℂ := ((goldenQ ^ 2 : ℝ) : ℂ)

theorem ordered_equality {rL rR t : ℂ} (hp : Passive rL rR t)
    (hX : 0 < extinction t)
    (heq : responseAsymmetry rL rR t / extinction t = gamma)
    (horder : ‖rR‖ ≤ ‖rL‖) :
    t = familyTransmission ∧ ∃ φ : ℝ,
      rL = familyLeft φ ∧ rR = familyRight φ := by
  obtain ⟨ht,hw,hd,hq⟩ := equality_magnitudes hp hX heq
  have hL : ‖rL‖ = 1 - goldenQ + goldenD := by
    unfold w at hw
    unfold d at hd
    rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hw
    linarith only [hw,hd]
  have hR : ‖rR‖ = goldenD - (1 - goldenQ) := by
    unfold w at hw
    unfold d at hd
    rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hw
    linarith only [hw,hd]
  have hgt : 0 < goldenQ ^ 2 := sq_pos_of_pos (by linarith [golden_properties.1])
  have hs := (parameter_identities rL rR t).2.2.2.2.1
  have hnorm : ‖t‖ = goldenQ ^ 2 := by
    rw [ht,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hgt]
  rw [hq,hd,hnorm] at hs
  have hprod := saturated_reflection_product (by simpa only [ht] using hp)
    hgt hL hR (by ring : 1 - goldenQ + goldenQ = 1) hs.symm
  have hA : 0 < 1 - goldenQ + goldenD := by
    have hgd : 0 ≤ goldenD :=
      mul_nonneg (by linarith [golden_properties.1]) (Real.sqrt_nonneg _)
    linarith [golden_properties.2.1]
  have hprod' : rL * rR =
      (((1 - goldenQ + goldenD) * (1 - goldenQ - goldenD) : ℝ) : ℂ) := by
    rw [hprod]
    congr 1
    ring
  obtain ⟨φ,hφL,hφR⟩ := phase_from_product hA hL hprod'
  exact ⟨ht,φ,hφL,hφR⟩

theorem equality_family_necessary {rL rR t : ℂ} (hp : Passive rL rR t)
    (hX : 0 < extinction t)
    (heq : responseAsymmetry rL rR t / extinction t = gamma) :
    t = familyTransmission ∧ ∃ φ : ℝ,
      (rL = familyLeft φ ∧ rR = familyRight φ) ∨
      (rR = familyLeft φ ∧ rL = familyRight φ) := by
  rcases le_total ‖rR‖ ‖rL‖ with ho | ho
  · obtain ⟨ht,φ,hL,hR⟩ := ordered_equality hp hX heq ho
    exact ⟨ht,φ,Or.inl ⟨hL,hR⟩⟩
  · have hswap : responseAsymmetry rR rL t = responseAsymmetry rL rR t := by
      unfold responseAsymmetry
      exact abs_sub_comm _ _
    obtain ⟨ht,φ,hL,hR⟩ := ordered_equality
      ((ScalarPhaseSymmetry.swap_passive rL rR t).mpr hp) hX (by rwa [hswap]) ho
    exact ⟨ht,φ,Or.inr ⟨hL,hR⟩⟩

theorem family_attains (φ : ℝ) :
    Passive (familyLeft φ) (familyRight φ) familyTransmission ∧
      0 < extinction familyTransmission ∧
      responseAsymmetry (familyLeft φ) (familyRight φ) familyTransmission /
        extinction familyTransmission = gamma := by
  let u : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have hus : star u = Complex.exp ((-φ : ℂ) * Complex.I) := by
    dsimp [u]
    rw [←Complex.exp_conj]
    simp
  have hL : familyLeft φ = u * left (1 - goldenQ) goldenD := by
    dsimp [familyLeft,left,u]
    ring
  have hR : familyRight φ = star u * right (1 - goldenQ) goldenD := by
    rw [hus]
    dsimp [familyRight,right]
    ring
  have hT : familyTransmission = trans (goldenQ ^ 2) := rfl
  have hp := (ScalarPhaseSymmetry.phase_twist_passive
    (left (1 - goldenQ) goldenD) (right (1 - goldenQ) goldenD)
    (trans (goldenQ ^ 2)) u hu).mpr golden_attained.1
  have hδ := (ScalarPhaseSymmetry.phase_twist_observables
    (left (1 - goldenQ) goldenD) (right (1 - goldenQ) goldenD)
    (trans (goldenQ ^ 2)) u hu).2.1
  have hresponse : responseAsymmetry (familyLeft φ) (familyRight φ) familyTransmission =
      responseAsymmetry (left (1 - goldenQ) goldenD) (right (1 - goldenQ) goldenD)
        (trans (goldenQ ^ 2)) := by
    rw [hL,hR,hT,responseAsymmetry_eq,responseAsymmetry_eq,hδ]
  refine ⟨by rwa [hL,hR,hT],?_,?_⟩
  · simpa only [hT] using golden_attained.2.1
  · rw [hresponse,hT]
    exact golden_attained.2.2

/-- Literal original Eq. (52), including necessity, every real phase, and port interchange. -/
theorem equality_family_iff (rL rR t : ℂ) :
    (Passive rL rR t ∧ 0 < extinction t ∧
      responseAsymmetry rL rR t / extinction t = gamma) ↔
    t = familyTransmission ∧ ∃ φ : ℝ,
      (rL = familyLeft φ ∧ rR = familyRight φ) ∨
      (rR = familyLeft φ ∧ rL = familyRight φ) := by
  constructor
  · rintro ⟨hp,hX,heq⟩
    exact equality_family_necessary hp hX heq
  · rintro ⟨ht,φ,(⟨hL,hR⟩|⟨hR,hL⟩)⟩
    · rw [ht,hL,hR]
      exact family_attains φ
    · rw [ht,hL,hR]
      have h := family_attains φ
      refine ⟨(ScalarPhaseSymmetry.swap_passive _ _ _).mpr h.1,h.2.1,?_⟩
      have hswap : responseAsymmetry (familyRight φ) (familyLeft φ) familyTransmission =
          responseAsymmetry (familyLeft φ) (familyRight φ) familyTransmission := by
        unfold responseAsymmetry
        exact abs_sub_comm _ _
      rw [hswap]
      exact h.2.2

/-- All clauses of original numbered Theorem 6.3, with its complete equality family. -/
theorem theorem63 :
    (∀ rL rR t : ℂ, Passive rL rR t → 0 < extinction t →
      responseAsymmetry rL rR t / extinction t ≤ gamma) ∧
    (∀ rL rR t : ℂ,
      (Passive rL rR t ∧ 0 < extinction t ∧
        responseAsymmetry rL rR t / extinction t = gamma) ↔
      t = familyTransmission ∧ ∃ φ : ℝ,
        (rL = familyLeft φ ∧ rR = familyRight φ) ∨
        (rR = familyLeft φ ∧ rL = familyRight φ)) :=
  ⟨golden_upper,equality_family_iff⟩

end GeneralizedResearch.GoldenClassification
