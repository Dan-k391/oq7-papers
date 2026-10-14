import PrescribedExtinction.StaticFourier

/-! Exact coordinate and zero-frequency facts for the existing explicit static
symbol. These supporting results do not identify the symbol with the physical
Newtonian distributional operator. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem staticSymbol_coordinate (ξ : Position) (v : Vector) (i : Fin 3) :
    staticSymbol ξ v i =
      ∑ j, ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ) * v j := by
  rw [staticSymbol_apply, tensorApply_rankOne]
  simp only [PiLp.smul_apply, smul_eq_mul, complexify, axisCoupling]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem staticSymbol_zero : staticSymbol (0 : Position) = 0 := by
  simp [staticSymbol, complexify]

theorem staticSymbol_zero_apply (v : Vector) : staticSymbol (0 : Position) v = 0 := by
  rw [staticSymbol_zero]
  rfl

theorem position_zero_volume : volume ({0} : Set Position) = 0 := by
  simp

theorem position_ae_ne_zero : ∀ᵐ ξ : Position ∂volume, ξ ≠ 0 := by
  rw [ae_iff]
  simp

/-- Assigning any continuous linear tensor at the origin changes only a null
set. No pointwise norm restriction at the origin is imposed. -/
def staticSymbolWithOrigin (A : Vector →L[ℂ] Vector) (ξ : Position) :
    Vector →L[ℂ] Vector :=
  if ξ = 0 then A else staticSymbol ξ

theorem staticSymbolWithOrigin_zero (A : Vector →L[ℂ] Vector) :
    staticSymbolWithOrigin A 0 = A := by
  simp [staticSymbolWithOrigin]

theorem staticSymbolWithOrigin_ae_eq (A : Vector →L[ℂ] Vector) :
    staticSymbolWithOrigin A =ᵐ[volume] staticSymbol := by
  filter_upwards [position_ae_ne_zero] with ξ hξ
  simp [staticSymbolWithOrigin, hξ]

theorem staticSymbolWithOrigin_apply_ae_eq (A : Vector →L[ℂ] Vector) (f : VectorL2) :
    (fun ξ => staticSymbolWithOrigin A ξ (f ξ)) =ᵐ[volume]
      fun ξ => staticSymbol ξ (f ξ) := by
  filter_upwards [staticSymbolWithOrigin_ae_eq A] with ξ hξ
  rw [hξ]

theorem staticSymbolWithOrigin_memLp (A : Vector →L[ℂ] Vector) (f : VectorL2) :
    MemLp (fun ξ => staticSymbolWithOrigin A ξ (f ξ)) 2 volume := by
  exact (memLp_congr_ae (staticSymbolWithOrigin_apply_ae_eq A f)).mpr
    (staticSymbol_memLp f)

def staticMultiplierWithOriginLp (A : Vector →L[ℂ] Vector) (f : VectorL2) : VectorL2 :=
  (staticSymbolWithOrigin_memLp A f).toLp _

theorem staticMultiplierWithOriginLp_eq (A : Vector →L[ℂ] Vector) (f : VectorL2) :
    staticMultiplierWithOriginLp A f = staticMultiplierLp f := by
  exact MemLp.toLp_congr _ _ (staticSymbolWithOrigin_apply_ae_eq A f)

end OQ7Prescribed
