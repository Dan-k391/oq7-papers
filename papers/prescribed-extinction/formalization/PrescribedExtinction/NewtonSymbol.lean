import PrescribedExtinction.StaticSymbolCoordinates
import PrescribedExtinction.NewtonSchwartz

/-! The exact scalar entries of the existing static tensor symbol, realized
as bounded functions and genuine tempered distributions. Their equality to
the Fourier transform of the physical Newton Hessian is a separate identity. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped ENNReal

def newtonHessianFrequency (i j : Fin 3) (ξ : Position) : ℂ :=
  ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem newtonHessianFrequency_staticSymbol (i j : Fin 3) (ξ : Position) :
    newtonHessianFrequency i j ξ = staticSymbol ξ (basisC j) i := by
  rw [staticSymbol_coordinate]
  simp [newtonHessianFrequency, basisC]

theorem newtonHessianFrequency_norm_le (i j : Fin 3) (ξ : Position) :
    ‖newtonHessianFrequency i j ξ‖ ≤ 1 := by
  rw [newtonHessianFrequency_staticSymbol]
  calc
    ‖staticSymbol ξ (basisC j) i‖ ≤ ‖staticSymbol ξ (basisC j)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖basisC j‖ := staticSymbol_apply_norm_le ξ (basisC j)
    _ = 1 := by simp [basisC]

theorem newtonHessianFrequency_zero (i j : Fin 3) :
    newtonHessianFrequency i j 0 = 0 := by
  simp [newtonHessianFrequency]

theorem newtonHessianFrequency_measurable (i j : Fin 3) :
    Measurable (newtonHessianFrequency i j) := by
  unfold newtonHessianFrequency
  fun_prop

theorem newtonHessianFrequency_memLp (i j : Fin 3) :
    MemLp (newtonHessianFrequency i j) ∞ volume := by
  exact memLp_top_of_bound (newtonHessianFrequency_measurable i j).aestronglyMeasurable 1
    (ae_of_all _ fun ξ => newtonHessianFrequency_norm_le i j ξ)

def newtonHessianFrequencyTempered (i j : Fin 3) : TemperedDistribution Position ℂ :=
  Lp.toTemperedDistribution ((newtonHessianFrequency_memLp i j).toLp (newtonHessianFrequency i j))

theorem newtonHessianFrequency_schwartz_integrable
    (φ : SchwartzMap Position ℂ) (i j : Fin 3) :
    Integrable (fun ξ => φ ξ * newtonHessianFrequency i j ξ) volume := by
  exact (φ.memLp 1 volume).integrable_mul (newtonHessianFrequency_memLp i j)

theorem newtonHessianFrequencyTempered_apply
    (φ : SchwartzMap Position ℂ) (i j : Fin 3) :
    newtonHessianFrequencyTempered i j φ =
      ∫ ξ : Position, φ ξ * newtonHessianFrequency i j ξ := by
  rw [newtonHessianFrequencyTempered, Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [(newtonHessianFrequency_memLp i j).coeFn_toLp] with ξ hξ
  rw [hξ]

end OQ7Prescribed
