import GeneralizedResearch.ChannelReciprocity

/-! Direct dipole-current proof of the dimensional parabola. The hypotheses
are passivity for every six-vector and transpose reciprocity, expressed through
the physical time-reversal antiunitary. No normality assumption is used. -/
noncomputable section
namespace CompactMaxwell
open GeneralizedResearch
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def dipoleWork (A : E →L[ℂ] E) (f : E) : ℝ := (inner ℂ f (A f)).im
def dipoleScattering (A : E →L[ℂ] E) (f : E) : ℝ := ‖A f‖ ^ 2
def dipoleAbsorption (A : E →L[ℂ] E) (f : E) : ℝ := dipoleWork A f - dipoleScattering A f
def dipoleScale (k : ℝ) : ℝ := 6 * Real.pi / k ^ 2

theorem dipole_work_reciprocity (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hrec : channelReciprocal C A) (f : E) :
    dipoleWork A (C.map f) = dipoleWork A f := by
  have h := hrec f (C.map f)
  rw [C.involution] at h
  exact congrArg Complex.im h

theorem dipole_unit_bounds (A : E →L[ℂ] E)
    (hpass : ∀ f, dipoleScattering A f ≤ dipoleWork A f) (f : E) (hf : ‖f‖ ^ 2 = 2) :
    0 ≤ dipoleWork A f ∧ dipoleWork A f ≤ 2 ∧
    0 ≤ dipoleAbsorption A f ∧
    dipoleAbsorption A f ≤ dipoleWork A f - (dipoleWork A f) ^ 2 / 2 := by
  have hn := norm_inner_le_norm (𝕜 := ℂ) f (A f)
  have hi := (Complex.abs_im_le_norm (inner ℂ f (A f))).trans hn
  have hs : dipoleWork A f ^ 2 ≤ 2 * dipoleScattering A f := by
    have hsq := (sq_le_sq₀ (abs_nonneg (inner ℂ f (A f)).im)
      (mul_nonneg (norm_nonneg f) (norm_nonneg (A f)))).mpr hi
    rw [mul_pow, hf, sq_abs] at hsq
    exact hsq
  have hsp := hpass f
  have hnon : 0 ≤ dipoleScattering A f := sq_nonneg _
  unfold dipoleAbsorption
  refine ⟨by linarith, ?_, by linarith, by linarith⟩
  nlinarith

theorem reciprocal_dipole_parabola (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hrec : channelReciprocal C A) (hpass : ∀ f, dipoleScattering A f ≤ dipoleWork A f)
    (f : E) (hf : ‖f‖ ^ 2 = 2) :
    0 ≤ dipoleWork A f ∧ dipoleWork A f ≤ 2 ∧
    |dipoleAbsorption A f - dipoleAbsorption A (C.map f)| ≤
      dipoleWork A f - dipoleWork A f ^ 2 / 2 := by
  have hp := dipole_unit_bounds A hpass f hf
  have hm := dipole_unit_bounds A hpass (C.map f) (by rw [C.norm_map]; exact hf)
  rw [dipole_work_reciprocity C A hrec f] at hm
  refine ⟨hp.1, hp.2.1, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith [hp.2.2.1, hp.2.2.2, hm.2.2.1, hm.2.2.2]

theorem dimensional_dipole_bound (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hrec : channelReciprocal C A) (hpass : ∀ f, dipoleScattering A f ≤ dipoleWork A f)
    (f : E) (hf : ‖f‖ ^ 2 = 2) {k : ℝ} (hk : 0 < k) :
    let X := dipoleScale k * dipoleWork A f
    0 ≤ X ∧ X ≤ 12 * Real.pi / k ^ 2 ∧
    |dipoleScale k * dipoleAbsorption A f - dipoleScale k * dipoleAbsorption A (C.map f)| ≤
      X - k ^ 2 * X ^ 2 / (12 * Real.pi) := by
  dsimp only
  have h := reciprocal_dipole_parabola C A hrec hpass f hf
  have hc : 0 < dipoleScale k := by unfold dipoleScale; positivity
  refine ⟨mul_nonneg hc.le h.1, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left h.2.1 hc.le
    convert hm using 1 <;> unfold dipoleScale <;> ring
  · rw [← mul_sub, abs_mul, abs_of_pos hc]
    have hm := mul_le_mul_of_nonneg_left h.2.2 hc.le
    convert hm using 1
    unfold dipoleScale
    field_simp
    ring

theorem dimensional_dipole_strict {X Δ k : ℝ} (hk : 0 < k) (hX : 0 < X)
    (hΔ : Δ ≤ X - k ^ 2 * X ^ 2 / (12 * Real.pi)) :
    Δ / X ≤ 1 - k ^ 2 * X / (12 * Real.pi) ∧ Δ / X < 1 := by
  have hd : Δ / X ≤ 1 - k ^ 2 * X / (12 * Real.pi) := by
    apply (div_le_iff₀ hX).mpr
    convert hΔ using 1 <;> ring
  refine ⟨hd, hd.trans_lt ?_⟩
  have hz : 0 < k ^ 2 * X / (12 * Real.pi) := by positivity
  linarith

end CompactMaxwell
