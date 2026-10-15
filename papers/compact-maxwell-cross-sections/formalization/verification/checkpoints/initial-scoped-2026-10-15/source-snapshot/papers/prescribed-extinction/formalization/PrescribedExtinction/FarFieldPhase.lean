import PrescribedExtinction.FarFieldGeometry
import PrescribedExtinction.ExteriorOutgoing

noncomputable section
namespace OQ7Prescribed

def scaledOutgoingPhase (k : ℝ) (x y : Position) : ℂ :=
  ((‖x‖ / ‖x - y‖ : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((k * (‖x - y‖ - ‖x‖) : ℝ) : ℂ))

theorem scaledOutgoingPhase_plane_error (k R : ℝ) (hR : 0 ≤ R)
    (x y : Position) (hx : 2 * R + 2 ≤ ‖x‖) (hy : ‖y‖ ≤ R) :
    ‖scaledOutgoingPhase k x y - Complex.exp (-Complex.I * ((k * inner ℝ (radialDirection x) y : ℝ) : ℂ))‖ ≤
      (2 * R + |k| * R ^ 2) / ‖x‖ := by
  have hr : 0 < ‖x‖ := by linarith
  have hhalf : 2 * ‖y‖ ≤ ‖x‖ := by linarith
  let a := k * (‖x - y‖ - ‖x‖)
  let b := -k * inner ℝ (radialDirection x) y
  have hb : Complex.I * (b : ℂ) = -Complex.I * ((k * inner ℝ (radialDirection x) y : ℝ) : ℂ) := by
    simp only [b, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hphase : ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤
      |k| * R ^ 2 / ‖x‖ := by
    apply (purePhase_norm_sub_le a b).trans
    have hd := displaced_distance_phase_error x y hr hhalf
    change 0 ≤ ‖x - y‖ - ‖x‖ + inner ℝ (radialDirection x) y ∧ _ at hd
    have hab : a - b = k * (‖x - y‖ - ‖x‖ + inner ℝ (radialDirection x) y) := by dsimp [a, b]; ring
    rw [hab, abs_mul, abs_of_nonneg hd.1]
    calc
      _ ≤ |k| * (‖y‖ ^ 2 / ‖x‖) := mul_le_mul_of_nonneg_left hd.2 (abs_nonneg k)
      _ = |k| * ‖y‖ ^ 2 / ‖x‖ := by ring
      _ ≤ _ := by gcongr
  have he : scaledOutgoingPhase k x y - Complex.exp (Complex.I * (b : ℂ)) =
      (((‖x‖ / ‖x - y‖ : ℝ) : ℂ) - 1) * Complex.exp (Complex.I * (a : ℂ)) +
        (Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))) := by
    dsimp [scaledOutgoingPhase, a]
    ring
  rw [← hb, he]
  calc
    _ ≤ ‖(((‖x‖ / ‖x - y‖ : ℝ) : ℂ) - 1) * Complex.exp (Complex.I * (a : ℂ))‖ +
        ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ := norm_add_le _ _
    _ = |‖x‖ / ‖x - y‖ - 1| +
        ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ := by
      rw [norm_mul, show ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 by simp [Complex.norm_exp], mul_one]
      congr 1
      norm_cast
    _ ≤ 2 * ‖y‖ / ‖x‖ + |k| * R ^ 2 / ‖x‖ :=
      add_le_add (displaced_inverse_amplitude_error x y hr hhalf) hphase
    _ ≤ 2 * R / ‖x‖ + |k| * R ^ 2 / ‖x‖ := by gcongr
    _ = _ := by ring

end OQ7Prescribed
