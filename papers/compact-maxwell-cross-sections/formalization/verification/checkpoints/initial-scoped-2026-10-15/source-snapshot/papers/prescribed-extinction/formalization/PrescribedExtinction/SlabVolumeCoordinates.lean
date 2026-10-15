import PrescribedExtinction.SlabGreen
import PrescribedExtinction.SphericalProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabCoordinateEquiv : ℂ × ℝ ≃ᵐ Position :=
  ((MeasurableEquiv.prodCongr Complex.measurableEquivRealProd (MeasurableEquiv.refl ℝ)).trans
    MeasurableEquiv.prodAssoc).trans
    (sphericalTripleEquiv.symm.trans (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

theorem slabCoordinateEquiv_apply (p : ℂ × ℝ) :
    slabCoordinateEquiv p = slabPosition p.1 p.2 := by
  rw [slabCoordinateEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply,
    sphericalTripleEquiv_symm_apply]
  rfl

theorem slabCoordinateEquiv_measurePreserving : MeasurePreserving slabCoordinateEquiv := by
  have h₁ := (Complex.volume_preserving_equiv_real_prod).prod (MeasurePreserving.id (volume : Measure ℝ))
  have h₂ : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ) :=
    volume_preserving_prodAssoc
  have h₃ := sphericalTripleEquiv_measurePreserving.symm
  exact ((PiLp.volume_preserving_toLp (Fin 3)).comp h₃).comp (h₂.comp h₁)

theorem integral_slabCoordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Position → E) : (∫ x : Position, f x) = ∫ p : ℂ × ℝ, f (slabPosition p.1 p.2) := by
  have he := slabCoordinateEquiv_measurePreserving.integral_comp
    slabCoordinateEquiv.measurableEmbedding f
  simpa only [slabCoordinateEquiv_apply] using he.symm

theorem slabPosition_sub (w y : ℂ) (z t : ℝ) :
    slabPosition w z - slabPosition y t = slabPosition (w - y) (z - t) := by
  ext i
  fin_cases i <;> simp [slabPosition]

end OQ7Prescribed
