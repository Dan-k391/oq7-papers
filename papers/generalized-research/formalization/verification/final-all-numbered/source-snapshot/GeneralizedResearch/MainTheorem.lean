import GeneralizedResearch.CanonicalPair
import GeneralizedResearch.ChannelAttainment
import GeneralizedResearch.FiniteHilbertBridge
import GeneralizedResearch.ReferenceIsometry

/-! # Full prescribed-overlap upper bound and exact finite channel sharpness

The upper statement quantifies over arbitrary-dimensional complex Hilbert
channel spaces, literal reciprocal contractions and lossless reciprocal
references. Sharpness is supplied by actual finite complex scattering matrices,
not by an uncompleted real semidefinite relaxation. -/

noncomputable section
universe u
namespace GeneralizedResearch

theorem all_branches_finite_attainment (p : OverlapParameters) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ChannelAttainment.FiniteAttainment p.rho r (p.envelope r) := by
  unfold OverlapParameters.envelope
  split_ifs with hlo hhi
  · exact ChannelAttainment.first_branch_attainment
      p.rho_pos p.rho_lt_one hr0 hlo
  · let m := p.middle r ⟨lt_of_not_ge hlo, hhi⟩
    have hm := ChannelAttainment.middle_branch_attainment m
    have hmr : m.r = r := p.middle_r r _
    rw [hmr] at hm
    exact hm
  · let t : ThirdBranch.Parameters := {
      rho := p.rho, r := r, rho_pos := p.rho_pos, rho_lt_one := p.rho_lt_one,
      rho_le_r := le_of_not_gt hhi, r_le_one := hr1 }
    exact ChannelAttainment.third_branch_attainment t

/-- Every signed extinction, including both endpoints, has an actual finite
complex reciprocal equality operator at the prescribed overlap. -/
theorem prescribed_extinction_attainment (p : OverlapParameters) (X : ℝ)
    (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    ChannelAttainment.FiniteAttainment p.rho (1 - X / 2)
      (p.envelope |1 - X / 2|) := by
  have hr : |1 - X / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h := all_branches_finite_attainment p |1 - X / 2| (abs_nonneg _) hr
  by_cases hpos : 0 ≤ 1 - X / 2
  · simpa only [abs_of_nonneg hpos] using h
  · have hneg := h.neg
    have heq : -|1 - X / 2| = 1 - X / 2 := by
      rw [abs_of_neg (lt_of_not_ge hpos), neg_neg]
    rwa [heq] at hneg

/-- Literal arbitrary-Hilbert-space upper half of original Theorem 7.1. -/
def Theorem71Upper (p : OverlapParameters) (X : ℝ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (C : ChannelConjugation E) (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E),
    channelReciprocal C S →
    channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap →
    ‖S‖ ≤ 1 →
    ∀ (v : E), ‖v‖ = 1 →
      ‖inner ℂ v (backgroundReverse C S₀ v)‖ = p.rho →
      channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap v = X →
      |channelAbsorption S v - channelAbsorption S (backgroundReverse C S₀ v)| ≤
        p.envelope |1 - X / 2|

/-- Original Theorem 7.1: the complete arbitrary-reference channel upper bound
and exact finite-dimensional attainability, at every prescribed extinction.
The explicit branch formula and unique middle parameter are `envelope`,
`middle_r` and `middle_parameter_exists_unique`; both transition formulas and
the necessary equality thresholds are checked in their dedicated modules. -/
theorem theorem71_matrix_witness (p : OverlapParameters) (X : ℝ) (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    Theorem71Upper.{u} p X ∧
      ChannelAttainment.FiniteAttainment p.rho (1 - X / 2)
        (p.envelope |1 - X / 2|) := by
  constructor
  · intro E instNorm instInner C S S₀ hS h₀ hpass v hv hover hX
    have h := CanonicalPair.full_overlap_upper p C S S₀ hS h₀ hpass v hv hover
    simpa only [hX] using h
  · exact prescribed_extinction_attainment p X hX0 hX4

/-- Exact attainability in the same Hilbert-space observables as the upper
statement, with an actual finite Euclidean channel space as witness. -/
def Theorem71Attained (p : OverlapParameters) (X : ℝ) : Prop :=
  ∃ (n : ℕ) (C : ChannelConjugation (EuclideanSpace ℂ (Fin n)))
    (S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (S₀ : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)),
    channelReciprocal C S ∧ channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap ∧
    ‖S‖ ≤ 1 ∧ ‖v‖ = 1 ∧ ‖inner ℂ v (backgroundReverse C S₀ v)‖ = p.rho ∧
    channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap v = X ∧
    |channelAbsorption S v - channelAbsorption S (backgroundReverse C S₀ v)| =
      p.envelope |1 - X / 2|

/-- Full original Theorem 7.1, with the upper and attained lower expressed in
the identical Hilbert channel model. The finite matrix-to-Hilbert conversion
is part of the proof, including norms, powers, unitary reference and reversal. -/
theorem theorem71 (p : OverlapParameters) (X : ℝ) (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    Theorem71Upper.{u} p X ∧ Theorem71Attained p X := by
  refine ⟨(theorem71_matrix_witness p X hX0 hX4).1, ?_⟩
  have h := FiniteHilbertBridge.finite_attainment_to_hilbert
    (prescribed_extinction_attainment p X hX0 hX4)
  have hs : 2 * (1 - (1 - X / 2)) = X := by ring
  simpa only [Theorem71Attained, FiniteHilbertBridge.HilbertAttainment, hs] using h

/-- The same upper conclusion under the manuscript's literal reference
condition `S₀†S₀=I`. Reciprocity proves the missing surjectivity, so no stronger
reference hypothesis is introduced in infinite dimension. -/
theorem theorem71_clm_reference {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (p : OverlapParameters)
    (C : ChannelConjugation E) (S S₀ : E →L[ℂ] E)
    (hS : channelReciprocal C S) (h₀ : channelReciprocal C S₀)
    (hunit : S₀.adjoint.comp S₀ = ContinuousLinearMap.id ℂ E)
    (hpass : ‖S‖ ≤ 1) (v : E) (hv : ‖v‖ = 1)
    (hρ : ‖inner ℂ v (C.map (S₀ v))‖ = p.rho) :
    |channelAbsorption S v - channelAbsorption S (C.map (S₀ v))| ≤
      p.envelope |1 - channelExtinction S S₀ v / 2| :=
  ReferenceIsometry.full_overlap_upper_clm p C S S₀ hS h₀ hunit hpass v hv hρ

#print axioms all_branches_finite_attainment
#print axioms prescribed_extinction_attainment
#print axioms theorem71

end GeneralizedResearch
