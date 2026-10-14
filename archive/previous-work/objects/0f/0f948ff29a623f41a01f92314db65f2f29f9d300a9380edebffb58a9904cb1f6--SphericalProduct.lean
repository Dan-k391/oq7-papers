import work.SphericalVolume
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def sphericalTripleEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

theorem sphericalTripleEquiv_apply (p : Fin 3 → ℝ) :
    sphericalTripleEquiv p = (p 0, (p 1, p 2)) := rfl

theorem sphericalTripleEquiv_symm_apply (p : ℝ × (ℝ × ℝ)) :
    sphericalTripleEquiv.symm p = ![p.1, p.2.1, p.2.2] := by
  apply sphericalTripleEquiv.injective
  simp [sphericalTripleEquiv_apply]

theorem sphericalTripleEquiv_measurePreserving : MeasurePreserving sphericalTripleEquiv := by
  exact ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

theorem sphericalTripleEquiv_domain : sphericalTripleEquiv ⁻¹'
    (Ioi (0 : ℝ) ×ˢ (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi)) = sphericalDomain := by
  ext p
  simp only [mem_preimage, sphericalTripleEquiv_apply, mem_prod, mem_Ioi, mem_Ioo,
    sphericalDomain, mem_setOf_eq]
  tauto

theorem sphericalDomain_product_integral (f : ℝ × (ℝ × ℝ) → ℝ) :
    (∫ p in sphericalDomain, f (p 0, (p 1, p 2))) =
      ∫ p in Ioi (0 : ℝ) ×ˢ (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi), f p := by
  rw [← sphericalTripleEquiv_domain]
  exact sphericalTripleEquiv_measurePreserving.setIntegral_preimage_emb
    sphericalTripleEquiv.measurableEmbedding f _

end OQ7Prescribed
