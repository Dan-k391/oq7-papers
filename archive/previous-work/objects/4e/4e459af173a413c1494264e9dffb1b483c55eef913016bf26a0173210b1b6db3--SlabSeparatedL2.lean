import PrescribedExtinction.SlabSourceGeometry
import work.SeparatedL2Product

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
open scoped ENNReal

theorem slabSeparatedFunction_memLp_two (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : MemLp w 2 volume) (hq : MemLp q 2 volume) :
    MemLp (slabSeparatedFunction w q) 2 volume := by
  have hp : MemLp (fun z : ℂ × ℝ => w z.1 * q z.2) 2 volume := by
    simpa only [Measure.volume_eq_prod] using separatedProduct_memLp_two w q hw hq
  have hm : MeasurePreserving (fun x : Position => slabCoordinateEquiv.symm x)
      (volume : Measure Position) (volume : Measure (ℂ × ℝ)) := slabCoordinateEquiv_measurePreserving.symm
  have he : MemLp ((fun z : ℂ × ℝ => w z.1 * q z.2) ∘
      (fun x : Position => slabCoordinateEquiv.symm x)) 2 volume := hp.comp_measurePreserving hm
  change MemLp (fun x : Position => w (slabHorizontalCoordinate x) * q (x 2)) 2 volume
  simpa only [Function.comp_def, slabCoordinateEquiv_symm_apply, slabSeparatedFunction,
    Measure.volume_eq_prod] using he

theorem slabSeparatedFunction_L2_norm (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : MemLp w 2 volume) (hq : MemLp q 2 volume) :
    ‖(slabSeparatedFunction_memLp_two w q hw hq).toLp (slabSeparatedFunction w q)‖ =
      ‖hw.toLp w‖ * ‖hq.toLp q‖ := by
  have hp : MemLp (fun z : ℂ × ℝ => w z.1 * q z.2) 2 volume := by
    simpa only [Measure.volume_eq_prod] using separatedProduct_memLp_two w q hw hq
  have hm : MeasurePreserving (fun x : Position => slabCoordinateEquiv.symm x)
      (volume : Measure Position) (volume : Measure (ℂ × ℝ)) := slabCoordinateEquiv_measurePreserving.symm
  have he := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hp.aestronglyMeasurable hm
  have hid : (fun z : ℂ × ℝ => w z.1 * q z.2) ∘ slabCoordinateEquiv.symm = slabSeparatedFunction w q := by
    funext x
    simp only [Function.comp_apply, slabCoordinateEquiv_symm_apply, slabSeparatedFunction]
  rw [hid] at he
  have hn := separatedProduct_norm w q hw hq
  rw [Lp.norm_toLp] at hn ⊢
  rw [he]
  simpa only [Measure.volume_eq_prod] using hn

end OQ7Prescribed
