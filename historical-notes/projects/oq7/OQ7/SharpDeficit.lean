import OQ7.Envelope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
namespace OQ7.ScalarEnvelope
open Filter
open scoped Topology

theorem sqrt_displacement_bound {T a x : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxx : x ≤ x0 T a) :
    0 ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) - y0 T a ∧
      Real.sqrt ((b T a) ^ 2 - x ^ 2) - y0 T a ≤
        x0 T a / y0 T a * (x0 T a - x) := by
  have hp := active_target_properties h
  have hy := hp.2.1
  have hx0 := hp.2.2.2.1
  have hxs := x0_sq h
  have hys := Real.sq_sqrt (radicand_nonneg h hx hxx)
  have hge : y0 T a ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) := by
    apply (Real.le_sqrt hy.le (radicand_nonneg h hx hxx)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxx) (by linarith : 0 ≤ x0 T a + x)]
  refine ⟨sub_nonneg.mpr hge, ?_⟩
  have hden : 0 < y0 T a := hy
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  have hid : (Real.sqrt ((b T a) ^ 2 - x ^ 2) - y0 T a) *
      (Real.sqrt ((b T a) ^ 2 - x ^ 2) + y0 T a) = (x0 T a - x) * (x0 T a + x) := by
    nlinarith only [hxs, hys]
  have hlow := mul_le_mul_of_nonneg_left (show 2 * y0 T a ≤
      Real.sqrt ((b T a) ^ 2 - x ^ 2) + y0 T a by linarith)
    (sub_nonneg.mpr hge)
  have hup := mul_le_mul_of_nonneg_left (show x0 T a + x ≤ 2 * x0 T a by linarith)
    (sub_nonneg.mpr hxx)
  rw [hid] at hlow
  nlinarith

theorem scaled_deficit_limit_of_phase {T a C : ℝ} (h : ActiveTarget T a)
    (x c scale : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j) (hxx : ∀ j, x j ≤ x0 T a)
    (hc : Tendsto (fun j => scale j * c j) atTop (𝓝 C))
    (hphase : Tendsto (fun j => scale j * (F T a (x j) - T * c j)) atTop (𝓝 0))
    (hsq : Tendsto (fun j => scale j * (x0 T a - x j) ^ 2) atTop (𝓝 0))
    (hysq : Tendsto (fun j => scale j *
      (Real.sqrt ((b T a) ^ 2 - (x j) ^ 2) - y0 T a) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => scale j * (D0 T a - 2 * x j)) atTop (𝓝 (alpha T a * C)) := by
  have hp := active_target_properties h
  have hden : s a * x0 T a ≠ 0 := (mul_pos hp.1 hp.2.2.2.1).ne'
  have hrem := ((hphase.const_mul (y0 T a)).add
    ((hsq.const_mul (y0 T a)).add ((hsq.add hysq).const_mul T))).div_const (s a * x0 T a)
  have ht := (hc.const_mul (alpha T a)).add hrem
  simp only [mul_zero, add_zero, zero_div] at ht
  apply ht.congr
  intro j
  have hid := tangent_remainder h (hx j) (hxx j)
  unfold alpha D0
  field_simp [hp.1.ne', hp.2.2.2.1.ne']
  nlinarith [congrArg (fun z : ℝ => scale j * z) hid]

#print axioms sqrt_displacement_bound
#print axioms scaled_deficit_limit_of_phase
end OQ7.ScalarEnvelope
