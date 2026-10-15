import PrescribedExtinction.TwoPieceL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def supportedConstMapLinear (μ : Measure α) (s : Set α) (A : E →L[ℂ] F) :
    SetSupportedL2 (E := E) μ s →ₗ[ℂ] SetSupportedL2 (E := F) μ s where
  toFun f := ⟨A.compLp (f : Lp E 2 μ), by
    change ∀ᵐ x ∂μ, x ∉ s → (A.compLp (f : Lp E 2 μ)) x = 0
    filter_upwards [A.coeFn_compLp (f : Lp E 2 μ), f.property] with x hx hf
    intro hxs
    rw [hx, hf hxs, map_zero]⟩
  map_add' f g := Subtype.ext (map_add (A.compLpL 2 μ) _ _)
  map_smul' z f := Subtype.ext (map_smul (A.compLpL 2 μ) z _)

def supportedConstMap (μ : Measure α) (s : Set α) (A : E →L[ℂ] F) :
    SetSupportedL2 (E := E) μ s →L[ℂ] SetSupportedL2 (E := F) μ s :=
  (supportedConstMapLinear μ s A).mkContinuous ‖A‖ fun f => A.norm_compLp_le (f : Lp E 2 μ)

theorem supportedConstMap_coe (μ : Measure α) (s : Set α) (A : E →L[ℂ] F)
    (f : SetSupportedL2 (E := E) μ s) :
    (supportedConstMap μ s A f : Lp F 2 μ) =ᵐ[μ] fun x => A ((f : Lp E 2 μ) x) :=
  A.coeFn_compLp _

def twoPieceSupportedMap (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (A B : E →L[ℂ] F) : SetSupportedL2 (E := E) μ s →L[ℂ] SetSupportedL2 (E := F) μ s :=
  supportedConstMap μ s A ∘L supportedSliceCLM μ s t ht +
    supportedConstMap μ s B ∘L
      (ContinuousLinearMap.id ℂ (SetSupportedL2 (E := E) μ s) - supportedSliceCLM μ s t ht)

theorem twoPieceSupportedMap_coe (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (A B : E →L[ℂ] F) (f : SetSupportedL2 (E := E) μ s) :
    (twoPieceSupportedMap μ s t ht A B f : Lp F 2 μ) =ᵐ[μ]
      fun x => if x ∈ t then A ((f : Lp E 2 μ) x) else B ((f : Lp E 2 μ) x) := by
  let g := supportedSliceCLM μ s t ht f
  filter_upwards [supportedSliceCLM_coe μ s t ht f,
    supportedConstMap_coe μ s A g, supportedConstMap_coe μ s B (f - g),
    Lp.coeFn_sub (f : Lp E 2 μ) (g : Lp E 2 μ),
    Lp.coeFn_add (supportedConstMap μ s A g : Lp F 2 μ)
      (supportedConstMap μ s B (f - g) : Lp F 2 μ)] with x hg ha hb hsub hadd
  change ((supportedConstMap μ s A g : Lp F 2 μ) +
    (supportedConstMap μ s B (f - g) : Lp F 2 μ)) x = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [ha, hb]
  change A ((g : Lp E 2 μ) x) + B (((f : Lp E 2 μ) - (g : Lp E 2 μ)) x) = _
  rw [hsub]
  change A ((g : Lp E 2 μ) x) + B ((f : Lp E 2 μ) x - (g : Lp E 2 μ) x) = _
  rw [hg]
  by_cases hx : x ∈ t <;> simp [hx]

theorem twoPieceSupportedMap_adjoint_inner (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (A B : E →L[ℂ] F) (f : SetSupportedL2 (E := E) μ s) (g : SetSupportedL2 (E := F) μ s) :
    inner ℂ (twoPieceSupportedMap μ s t ht A B f) g =
      inner ℂ f (twoPieceSupportedMap μ s t ht A.adjoint B.adjoint g) := by
  change inner ℂ (twoPieceSupportedMap μ s t ht A B f : Lp F 2 μ) (g : Lp F 2 μ) =
    inner ℂ (f : Lp E 2 μ) (twoPieceSupportedMap μ s t ht A.adjoint B.adjoint g : Lp E 2 μ)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [twoPieceSupportedMap_coe μ s t ht A B f,
    twoPieceSupportedMap_coe μ s t ht A.adjoint B.adjoint g] with x hx hy
  rw [hx, hy]
  by_cases hxt : x ∈ t <;> simp only [hxt, ite_true, ite_false]
  · exact (A.adjoint_inner_right _ _).symm
  · exact (B.adjoint_inner_right _ _).symm

end OQ7Prescribed
