import PrescribedExtinction.SlabRadialWindow
import PrescribedExtinction.SlabPolar

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem slabWindow_circle (w : ℂ → ℂ) (x : ℂ) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, w (x - circleMap 0 r θ)) =
      (2 * Real.pi) • apertureCircleJet 0 w x r := by
  have hf : (fun θ => w (x - circleMap 0 r θ)) =
      fun θ => w (circleMap x (-r) θ) := by
    funext θ
    congr 1
    simp [circleMap]
    ring
  rw [hf, apertureCircleJet_zero, ← Real.circleAverage_neg_radius (R := r)]
  rw [Real.circleAverage_def, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hp : Function.Periodic (fun θ => w (circleMap x (-r) θ)) (2 * Real.pi) := by
    intro θ
    exact congrArg w (periodic_circleMap x (-r) θ)
  have he := hp.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at he
  exact he

end OQ7Prescribed
