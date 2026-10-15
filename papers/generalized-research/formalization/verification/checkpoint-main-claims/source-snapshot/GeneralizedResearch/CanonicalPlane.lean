import GeneralizedResearch.ChannelCoordinates
import GeneralizedResearch.HilbertCompression
import GeneralizedResearch.CanonicalEnvelope

/-! Actual canonical input-plane compression in a Hilbert channel space of
arbitrary dimension. The slack and contraction matrices are derived from the
operator and actual vectors; no finite auxiliary-coordinate expansion is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch
namespace CanonicalPlane
open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def inputs (e : Fin 2 → E) (i : Fin 2) : E := if i = 0 then e i else Complex.I • e i
def outputs (C : ChannelConjugation E) (e : Fin 2 → E) : Fin 2 → E :=
  fun i => C.map (inputs e i)
def images (T : E →L[ℂ] E) (e : Fin 2 → E) : Fin 2 → E := T ∘ inputs e
def B (C : ChannelConjugation E) (T : E →L[ℂ] E) (e : Fin 2 → E) : Mat2 :=
  HilbertCompression.B (outputs C e) (images T e)
def Q (T : E →L[ℂ] E) (e : Fin 2 → E) : Mat2 := Matrix.gram ℝ (images T e)
def incident (p : OverlapParameters) (e : Fin 2 → E) : E :=
  p.inputP • inputs e 0 + p.inputQ • inputs e 1
def reversedIncident (p : OverlapParameters) (e : Fin 2 → E) : E :=
  p.inputP • inputs e 0 - p.inputQ • inputs e 1

theorem inputs_orthonormal (e : Fin 2 → E) (he : Orthonormal ℂ e) :
    Orthonormal ℂ (inputs e) := by
  rw [orthonormal_iff_ite] at he ⊢
  intro i j
  fin_cases i <;> fin_cases j
  all_goals dsimp [inputs]
  all_goals simp only [inner_smul_left, inner_smul_right, he]
  all_goals norm_num [Complex.I_sq]

theorem real_orthonormal (u : Fin 2 → E) (hu : Orthonormal ℂ u) : Orthonormal ℝ u := by
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  rw [real_inner_eq_re_inner ℂ, hu]
  split_ifs <;> rfl

theorem outputs_orthonormal (C : ChannelConjugation E) (e : Fin 2 → E)
    (he : Orthonormal ℂ e) : Orthonormal ℝ (outputs C e) := by
  apply real_orthonormal
  have hi := orthonormal_iff_ite.mp (inputs_orthonormal e he)
  rw [orthonormal_iff_ite]
  intro i j
  rw [outputs, outputs, C.inner_swap, hi]
  simp [eq_comm]

theorem B_hermitian (C : ChannelConjugation E) (T : E →L[ℂ] E)
    (e : Fin 2 → E) (hT : channelReciprocal C T) : (B C T e).IsHermitian := by
  ext i j
  simp only [B, HilbertCompression.B, outputs, images, Function.comp_apply,
    Matrix.conjTranspose_apply, star_trivial]
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, hT]

theorem relaxation (C : ChannelConjugation E) (T : E →L[ℂ] E)
    (e : Fin 2 → E) (he : Orthonormal ℂ e) (hT : channelReciprocal C T) :
    (Q T e - B C T e ^ 2).PosSemidef :=
  HilbertCompression.symmetric_projection_gap_posSemidef
    (outputs C e) (images T e) (outputs_orthonormal C e he) (B_hermitian C T e hT)

theorem contraction (T : E →L[ℂ] E) (e : Fin 2 → E)
    (he : Orthonormal ℂ e) (hpass : ‖T‖ ≤ 1) : ((1 : Mat2) - Q T e).PosSemidef := by
  have h := HilbertCompression.contraction_gram_posSemidef
    (inputs e) (real_orthonormal _ (inputs_orthonormal e he)) (T.restrictScalars ℝ)
    (by simpa only [ContinuousLinearMap.norm_restrictScalars] using hpass)
  exact h

theorem outputs_explicit (C : ChannelConjugation E) (e : Fin 2 → E)
    (hfix : ∀ i, C.map (e i) = e i) :
    outputs C e 0 = inputs e 0 ∧ outputs C e 1 = -inputs e 1 := by
  simp [outputs, inputs, C.map_smul, hfix]

theorem absorption_difference (p : OverlapParameters) (T : E →L[ℂ] E)
    (e : Fin 2 → E) :
    |channelAbsorption T (incident p e) - channelAbsorption T (reversedIncident p e)| =
      2 * p.d * |Q T e 0 1| := by
  have hnorm : ∀ x y : E, ‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 = 4 * inner ℝ x y := by
    intro x y
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  unfold channelAbsorption incident reversedIncident
  rw [map_add, map_sub]
  simp only [ContinuousLinearMap.map_smul_of_tower]
  have h := hnorm (p.inputP • T (inputs e 0)) (p.inputQ • T (inputs e 1))
  rw [real_inner_smul_left, real_inner_smul_right] at h
  have hd := p.input_product
  have hd' := congrArg (fun z : ℝ => z * inner ℝ (T (inputs e 0)) (T (inputs e 1))) hd
  change |(1 - ‖p.inputP • T (inputs e 0) + p.inputQ • T (inputs e 1)‖ ^ 2) -
    (1 - ‖p.inputP • T (inputs e 0) - p.inputQ • T (inputs e 1)‖ ^ 2)| = _
  have heq : (1 - ‖p.inputP • T (inputs e 0) + p.inputQ • T (inputs e 1)‖ ^ 2) -
      (1 - ‖p.inputP • T (inputs e 0) - p.inputQ • T (inputs e 1)‖ ^ 2) =
      -(2 * p.d) * Q T e 0 1 := by
    change _ = -(2 * p.d) * inner ℝ (T (inputs e 0)) (T (inputs e 1))
    nlinarith
  rw [heq, abs_mul, abs_neg, abs_of_pos (mul_pos (by norm_num) p.d_pos)]

theorem extinction_forward (p : OverlapParameters) (C : ChannelConjugation E)
    (T : E →L[ℂ] E) (e : Fin 2 → E) (hT : channelReciprocal C T)
    (hfix : ∀ i, C.map (e i) = e i) :
    1 - channelExtinction T (ContinuousLinearMap.id ℂ E) (incident p e) / 2 =
      (p.W * B C T e).trace := by
  obtain ⟨h0,h1⟩ := outputs_explicit C e hfix
  have hs := (B_hermitian C T e hT).apply 0 1
  have hb : B C T e 0 1 = -inner ℝ (inputs e 1) (T (inputs e 0)) := by
    rw [← hs]
    change inner ℝ (outputs C e 1) (T (inputs e 0)) = _
    rw [h1, inner_neg_left]
  have h00 : B C T e 0 0 = inner ℝ (inputs e 0) (T (inputs e 0)) := by
    change inner ℝ (outputs C e 0) (T (inputs e 0)) = _
    rw [h0]
  have h11 : B C T e 1 1 = -inner ℝ (inputs e 1) (T (inputs e 1)) := by
    change inner ℝ (outputs C e 1) (T (inputs e 1)) = _
    rw [h1, inner_neg_left]
  have h01 : inner ℝ (inputs e 0) (T (inputs e 1)) = B C T e 0 1 := by
    change _ = inner ℝ (outputs C e 0) (T (inputs e 1))
    rw [h0]
  unfold channelExtinction
  simp only [ContinuousLinearMap.id_apply]
  change 1 - 2 * (1 - inner ℝ (incident p e) (T (incident p e))) / 2 = _
  simp only [incident, map_add, ContinuousLinearMap.map_smul_of_tower, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [OverlapParameters.W, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, zero_mul, add_zero, zero_add]
  rw [h00, h11, h01, hb]
  have hp := congrArg (fun z : ℝ => z * inner ℝ (inputs e 0) (T (inputs e 0))) p.inputP_sq
  have hq := congrArg (fun z : ℝ => z * inner ℝ (inputs e 1) (T (inputs e 1))) p.inputQ_sq
  nlinarith

theorem hilbert_canonical_envelope (p : OverlapParameters) (C : ChannelConjugation E)
    (T : E →L[ℂ] E) (e : Fin 2 → E) (he : Orthonormal ℂ e)
    (hT : channelReciprocal C T) (hpass : ‖T‖ ≤ 1)
    (hfix : ∀ i, C.map (e i) = e i) :
    |channelAbsorption T (incident p e) - channelAbsorption T (reversedIncident p e)| ≤
      p.envelope |1 - channelExtinction T (ContinuousLinearMap.id ℂ E) (incident p e) / 2| := by
  rw [absorption_difference, extinction_forward p C T e hT hfix]
  exact p.all_branches_upper_bound _ (B C T e) (Q T e)
    (B_hermitian C T e hT) (Matrix.isHermitian_gram ℝ _)
    (relaxation C T e he hT) (contraction T e he hpass) rfl

end CanonicalPlane
end GeneralizedResearch
