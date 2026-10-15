import GeneralizedResearch.CanonicalPlane
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Actual phase normalization and construction of the two conjugation-fixed
orthonormal vectors from a unit input and its antiunitary reverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch
namespace CanonicalPair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

theorem map_real_smul (C : ChannelConjugation E) (r : ℝ) (u : E) :
    C.map (r • u) = r • C.map u := by
  change C.map ((r : ℂ) • u) = (r : ℂ) • C.map u
  rw [C.map_smul]
  simp

theorem map_sub (C : ChannelConjugation E) (u v : E) :
    C.map (u - v) = C.map u - C.map v := by
  rw [sub_eq_add_neg, C.map_add]
  have h : C.map (-v) = -C.map v := by
    simpa using C.map_smul (-1) v
  rw [h, sub_eq_add_neg]

theorem unit_phase_exists (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hz : ‖z‖ = ρ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ star a * star a * z = (ρ : ℂ) := by
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (z / (ρ : ℂ)) (by norm_num : 0 < (2 : ℕ))
  have hn := congrArg norm ha
  simp only [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ, hz, div_self hρ.ne'] at hn
  have hna : ‖a‖ = 1 := by nlinarith [norm_nonneg a]
  have hane : a ≠ 0 := by intro h; simp [h] at hna
  have hstar : star a = a⁻¹ := by
    simpa using (RCLike.inv_eq_conj hna).symm
  have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  refine ⟨a,hna,?_⟩
  rw [hstar]
  field_simp [hane, hρne] at ha ⊢
  linear_combination -ha

theorem phase_normalizes_pair (C : ChannelConjugation E) (u : E)
    (p : OverlapParameters) (hρ : ‖inner ℂ u (C.map u)‖ = p.rho) :
    ∃ a : ℂ, ‖a‖ = 1 ∧
      inner ℂ (a • u) (C.map (a • u)) = (p.rho : ℂ) := by
  obtain ⟨a,ha,hz⟩ := unit_phase_exists _ p.rho_pos hρ
  refine ⟨a,ha,?_⟩
  rw [C.map_smul, inner_smul_left, inner_smul_right]
  simpa only [mul_assoc, starRingEnd_apply] using hz

def first (p : OverlapParameters) (C : ChannelConjugation E) (u : E) : E :=
  (2 * p.inputP)⁻¹ • (u + C.map u)
def second (p : OverlapParameters) (C : ChannelConjugation E) (u : E) : E :=
  (-Complex.I) • ((2 * p.inputQ)⁻¹ • (u - C.map u))
def frame (p : OverlapParameters) (C : ChannelConjugation E) (u : E) : Fin 2 → E :=
  ![first p C u, second p C u]

theorem sum_diff_inner (p : OverlapParameters) (C : ChannelConjugation E) (u : E)
    (hu : ‖u‖ = 1) (hρ : inner ℂ u (C.map u) = (p.rho : ℂ)) :
    inner ℂ (u + C.map u) (u - C.map u) = 0 := by
  have hv : ‖C.map u‖ = 1 := (C.norm_map u).trans hu
  have hρ' : inner ℂ (C.map u) u = (p.rho : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (C.map u) u, hρ]
    simp
  simp only [inner_add_left, inner_sub_right, inner_self_eq_norm_sq_to_K,
    hu, hv, hρ, hρ']
  ring

theorem first_norm (p : OverlapParameters) (C : ChannelConjugation E) (u : E)
    (hu : ‖u‖ = 1) (hρ : inner ℂ u (C.map u) = (p.rho : ℂ)) :
    ‖first p C u‖ = 1 := by
  have hv : ‖C.map u‖ = 1 := (C.norm_map u).trans hu
  have hr : inner ℝ u (C.map u) = p.rho := by rw [real_inner_eq_re_inner ℂ,hρ]; rfl
  have h := norm_add_sq_real u (C.map u)
  rw [hu,hv,hr] at h
  have hsum : ‖u + C.map u‖ = 2 * p.inputP := by
    nlinarith [p.inputP_sq,p.inputP_pos,norm_nonneg (u + C.map u)]
  rw [first,norm_smul,hsum,Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) p.inputP_pos))]
  field_simp [p.inputP_pos.ne']

theorem second_norm (p : OverlapParameters) (C : ChannelConjugation E) (u : E)
    (hu : ‖u‖ = 1) (hρ : inner ℂ u (C.map u) = (p.rho : ℂ)) :
    ‖second p C u‖ = 1 := by
  have hv : ‖C.map u‖ = 1 := (C.norm_map u).trans hu
  have hr : inner ℝ u (C.map u) = p.rho := by rw [real_inner_eq_re_inner ℂ,hρ]; rfl
  have h := norm_sub_sq_real u (C.map u)
  rw [hu,hv,hr] at h
  have hsum : ‖u - C.map u‖ = 2 * p.inputQ := by
    nlinarith [p.inputQ_sq,p.inputQ_pos,norm_nonneg (u - C.map u)]
  rw [second,norm_smul,norm_neg,Complex.norm_I,one_mul,norm_smul,hsum,Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) p.inputQ_pos))]
  field_simp [p.inputQ_pos.ne']

theorem frame_orthonormal (p : OverlapParameters) (C : ChannelConjugation E) (u : E)
    (hu : ‖u‖ = 1) (hρ : inner ℂ u (C.map u) = (p.rho : ℂ)) :
    Orthonormal ℂ (frame p C u) := by
  constructor
  · intro i
    fin_cases i
    · exact first_norm p C u hu hρ
    · exact second_norm p C u hu hρ
  · intro i j hij
    have hzero : inner ℂ (first p C u) (second p C u) = 0 := by
      rw [first,second,inner_smul_left_eq_smul,inner_smul_right,
        inner_smul_right_eq_smul, sum_diff_inner p C u hu hρ]
      simp
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hzero
    · rw [← inner_conj_symm]
      simp [frame,hzero]
    · exact (hij rfl).elim

theorem frame_fixed (p : OverlapParameters) (C : ChannelConjugation E) (u : E)
    (i : Fin 2) : C.map (frame p C u i) = frame p C u i := by
  fin_cases i
  · change C.map (first p C u) = first p C u
    rw [first,map_real_smul,C.map_add,C.involution u]
    congr 1
    abel
  · change C.map (second p C u) = second p C u
    rw [second,C.map_smul,map_real_smul,map_sub,C.involution u]
    simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
    rw [show C.map u - u = -(u - C.map u) by abel, smul_neg, smul_neg, neg_smul]

theorem incident_eq (p : OverlapParameters) (C : ChannelConjugation E) (u : E) :
    CanonicalPlane.incident p (frame p C u) = u := by
  change p.inputP • ((2 * p.inputP)⁻¹ • (u + C.map u)) +
    p.inputQ • (Complex.I • ((-Complex.I) • ((2 * p.inputQ)⁻¹ • (u - C.map u)))) = u
  have hi (w : E) : Complex.I • ((-Complex.I) • w) = w := by simp [smul_smul]
  rw [hi]
  have hp : p.inputP * (2 * p.inputP)⁻¹ = (1 / 2 : ℝ) := by field_simp [p.inputP_pos.ne']
  have hq : p.inputQ * (2 * p.inputQ)⁻¹ = (1 / 2 : ℝ) := by field_simp [p.inputQ_pos.ne']
  rw [smul_smul, hp, smul_smul, hq]
  module

theorem reversed_eq (p : OverlapParameters) (C : ChannelConjugation E) (u : E) :
    CanonicalPlane.reversedIncident p (frame p C u) = C.map u := by
  have h := CanonicalPlane.outputs_explicit C (frame p C u) (frame_fixed p C u)
  change C.map (CanonicalPlane.inputs (frame p C u) 0) =
    CanonicalPlane.inputs (frame p C u) 0 ∧
    C.map (CanonicalPlane.inputs (frame p C u) 1) =
    -CanonicalPlane.inputs (frame p C u) 1 at h
  calc
    CanonicalPlane.reversedIncident p (frame p C u) =
        C.map (CanonicalPlane.incident p (frame p C u)) := by
      rw [CanonicalPlane.incident, C.map_add, map_real_smul, map_real_smul, h.1, h.2]
      unfold CanonicalPlane.reversedIncident
      rw [smul_neg,sub_eq_add_neg]
    _ = C.map u := by rw [incident_eq]

theorem unit_phase_absorption (T : E →L[ℂ] E) (a : ℂ) (ha : ‖a‖ = 1) (u : E) :
    channelAbsorption T (a • u) = channelAbsorption T u := by
  simp only [channelAbsorption, map_smul, norm_smul, ha, one_mul]

theorem unit_phase_extinction (T : E →L[ℂ] E) (a : ℂ) (ha : ‖a‖ = 1) (u : E) :
    channelExtinction T (ContinuousLinearMap.id ℂ E) (a • u) =
      channelExtinction T (ContinuousLinearMap.id ℂ E) u := by
  have hunit : (starRingEnd ℂ) a * a = 1 := by
    simpa only [ha, one_pow, RCLike.ofReal_one] using RCLike.conj_mul a
  have hunit' : a * (starRingEnd ℂ) a = 1 := by rw [mul_comm,hunit]
  unfold channelExtinction
  simp only [ContinuousLinearMap.id_apply, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, hunit', one_mul]

/-- The complete overlap upper bound for an arbitrary input and genuine
antiunitary conjugation, with no canonical-coordinate hypothesis. -/
theorem general_conjugation_upper (p : OverlapParameters) (C : ChannelConjugation E)
    (T : E →L[ℂ] E) (hT : channelReciprocal C T) (hpass : ‖T‖ ≤ 1)
    (u : E) (hu : ‖u‖ = 1) (hρ : ‖inner ℂ u (C.map u)‖ = p.rho) :
    |channelAbsorption T u - channelAbsorption T (C.map u)| ≤
      p.envelope |1 - channelExtinction T (ContinuousLinearMap.id ℂ E) u / 2| := by
  obtain ⟨a,ha,hreal⟩ := phase_normalizes_pair C u p hρ
  have hunit : ‖a • u‖ = 1 := by rw [norm_smul,ha,hu,mul_one]
  have h := CanonicalPlane.hilbert_canonical_envelope p C T (frame p C (a • u))
    (frame_orthonormal p C (a • u) hunit hreal) hT hpass (frame_fixed p C (a • u))
  rw [incident_eq, reversed_eq, unit_phase_extinction T a ha u,
    unit_phase_absorption T a ha u, C.map_smul] at h
  have hstar : ‖star a‖ = 1 := by simpa using ha
  rwa [unit_phase_absorption T (star a) hstar] at h

/-- Full general-reference upper bound of the prescribed-overlap theorem.
The unitary lossless reference is normalized by an actual isometry, preserving
the powers; the input-plane constraints are derived in arbitrary dimension. -/
theorem full_overlap_upper (p : OverlapParameters) (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (hpass : ‖S‖ ≤ 1) (u : E) (hu : ‖u‖ = 1)
    (hρ : ‖inner ℂ u (backgroundReverse C S₀ u)‖ = p.rho) :
    |channelAbsorption S u - channelAbsorption S (backgroundReverse C S₀ u)| ≤
      p.envelope |1 - channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u / 2| := by
  have h := general_conjugation_upper p (backgroundConjugation C S₀ h₀)
    (normalizedScatterer S S₀) (normalizedScatterer_reciprocal C S S₀ hS h₀)
    ((normalizedScatterer_norm_le S S₀).trans hpass) u hu hρ
  simpa only [backgroundConjugation, normalizedScatterer_absorption,
    normalizedScatterer_extinction] using h

end CanonicalPair
end GeneralizedResearch
