import work.SlabVolumeCoordinates
import PrescribedExtinction.SmoothOutgoingFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabHorizontalCoordinate (x : Position) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

theorem slabCoordinateEquiv_symm_apply (x : Position) :
    slabCoordinateEquiv.symm x = (slabHorizontalCoordinate x, x 2) := by
  apply slabCoordinateEquiv.injective
  rw [slabCoordinateEquiv.apply_symm_apply, slabCoordinateEquiv_apply]
  ext i
  fin_cases i <;> simp [slabHorizontalCoordinate, slabPosition]

def slabCoordinateHomeomorph : ℂ × ℝ ≃ₜ Position where
  toEquiv := slabCoordinateEquiv.toEquiv
  continuous_toFun := by
    change Continuous (fun p : ℂ × ℝ => slabCoordinateEquiv p)
    simp_rw [slabCoordinateEquiv_apply]
    unfold slabPosition
    fun_prop
  continuous_invFun := by
    change Continuous (fun x : Position => slabCoordinateEquiv.symm x)
    simp_rw [slabCoordinateEquiv_symm_apply]
    unfold slabHorizontalCoordinate
    fun_prop

def slabProductFunction (w : ℂ → ℂ) (q : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := w p.1 * q p.2

theorem slabProductFunction_hasCompactSupport (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : HasCompactSupport w) (hq : HasCompactSupport q) : HasCompactSupport (slabProductFunction w q) := by
  have hs : Function.support (slabProductFunction w q) ⊆ tsupport w ×ˢ tsupport q := by
    intro p hp
    have hn : w p.1 ≠ 0 ∧ q p.2 ≠ 0 := mul_ne_zero_iff.mp hp
    exact ⟨subset_closure hn.1, subset_closure hn.2⟩
  exact (hw.prod hq).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs (hw.prod hq).isClosed)

def slabSeparatedFunction (w : ℂ → ℂ) (q : ℝ → ℂ) (x : Position) : ℂ :=
  w (slabHorizontalCoordinate x) * q (x 2)

theorem slabSeparatedFunction_at_slab (w : ℂ → ℂ) (q : ℝ → ℂ) (y : ℂ) (t : ℝ) :
    slabSeparatedFunction w q (slabPosition y t) = w y * q t := by
  simp [slabSeparatedFunction, slabPosition, slabHorizontalCoordinate]

theorem slabSeparatedFunction_hasCompactSupport (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : HasCompactSupport w) (hq : HasCompactSupport q) : HasCompactSupport (slabSeparatedFunction w q) := by
  have he : slabSeparatedFunction w q = slabProductFunction w q ∘ slabCoordinateHomeomorph.symm := by
    funext x
    change _ = slabProductFunction w q (slabCoordinateEquiv.symm x)
    rw [slabCoordinateEquiv_symm_apply]
    rfl
  rw [he]
  exact (slabProductFunction_hasCompactSupport w q hw hq).comp_homeomorph _

theorem slabSeparatedFunction_contDiff (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (slabSeparatedFunction w q) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) slabHorizontalCoordinate := by
    have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position => x i) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp (hp 0)).add
      ((Complex.ofRealCLM.contDiff.comp (hp 1)).mul contDiff_const)
  exact (hw.comp hh).mul (hq.comp (by fun_prop))

end OQ7Prescribed
