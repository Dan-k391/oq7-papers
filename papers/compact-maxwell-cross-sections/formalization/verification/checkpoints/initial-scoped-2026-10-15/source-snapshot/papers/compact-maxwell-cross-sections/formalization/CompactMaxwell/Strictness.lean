import QuarticMaxwell.RadiationOperator
import Mathlib.Tactic

/-! Proposition 2.1 with precisely its stated hypotheses: actual continuous
sphere far fields, their full integral, the forward optical law and passivity. -/
noncomputable section
namespace CompactMaxwell
open MeasureTheory Set OQ7Prescribed

def scattering (F : UnitSphere → Vector) : ℝ := ∫ n, ‖F n‖ ^ 2 ∂sphereArea

def directivity (F : UnitSphere → Vector) (e : Vector) (d : UnitSphere) : ℝ :=
  4 * Real.pi * ‖inner ℂ e (F d)‖ ^ 2 / scattering F

theorem zero_scattering_iff (F : UnitSphere → Vector) (hF : Continuous F) :
    scattering F = 0 ↔ F = 0 := by
  constructor
  · intro hz
    let : sphereArea.IsOpenPosMeasure := by unfold sphereArea; infer_instance
    have hi : Integrable (fun n => ‖F n‖ ^ 2) sphereArea :=
      (hF.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hae : (fun n => ‖F n‖ ^ 2) =ᵐ[sphereArea] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hz
    have h := Measure.eq_of_ae_eq hae (hF.norm.pow 2) continuous_const
    funext n
    have hn := congrFun h n
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · intro hz
    simp [scattering, hz]

theorem positive_scattering (F : UnitSphere → Vector) (hF : Continuous F)
    {k X : ℝ} (hk : 0 < k) (hX : 0 < X) (e : Vector) (d : UnitSphere)
    (hopt : X = 4 * Real.pi / k * (inner ℂ e (F d)).im) :
    0 < scattering F := by
  have hS : 0 ≤ scattering F := integral_nonneg fun _ => sq_nonneg _
  by_contra hn
  have hz : scattering F = 0 := le_antisymm (le_of_not_gt hn) hS
  have hf := (zero_scattering_iff F hF).mp hz
  simp [hf] at hopt
  linarith

theorem forward_nonzero (F : UnitSphere → Vector) {k X : ℝ}
    (hX : 0 < X) (e : Vector) (d : UnitSphere)
    (hopt : X = 4 * Real.pi / k * (inner ℂ e (F d)).im) :
    inner ℂ e (F d) ≠ 0 := by
  intro hz
  rw [hz] at hopt
  simp only [Complex.zero_im, mul_zero] at hopt
  linarith

theorem forward_directivity_floor (F : UnitSphere → Vector) (hF : Continuous F)
    {k X : ℝ} (hk : 0 < k) (hX : 0 < X) (e : Vector) (d : UnitSphere)
    (hopt : X = 4 * Real.pi / k * (inner ℂ e (F d)).im) :
    0 < directivity F e d ∧
      k ^ 2 * X / (4 * Real.pi * directivity F e d) ≤ scattering F / X := by
  have hS := positive_scattering F hF hk hX e d hopt
  have hn : 0 < ‖inner ℂ e (F d)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (forward_nonzero F hX e d hopt))
  have hD : 0 < directivity F e d := by unfold directivity; positivity
  refine ⟨hD, ?_⟩
  have hi : (inner ℂ e (F d)).im ^ 2 ≤ ‖inner ℂ e (F d)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (inner ℂ e (F d)).re]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.pi * directivity F e d) hX).mpr
  have he : 4 * Real.pi * directivity F e d * scattering F =
      16 * Real.pi ^ 2 * ‖inner ℂ e (F d)‖ ^ 2 := by
    unfold directivity
    field_simp
    ring
  rw [mul_comm (scattering F), he]
  have hx : k * X = 4 * Real.pi * (inner ℂ e (F d)).im := by
    rw [hopt]
    field_simp
  have hx2 := congrArg (fun r : ℝ => r ^ 2) hx
  nlinarith [mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 16 * Real.pi ^ 2)]

theorem strict_bound_and_directivity (Fh Fl : UnitSphere → Vector)
    (hFh : Continuous Fh) (hFl : Continuous Fl) {k X Ah Al : ℝ}
    (hk : 0 < k) (hX : 0 < X) (hAh : 0 ≤ Ah) (hAl : 0 ≤ Al) (horder : Al ≤ Ah)
    (hbalh : X = Ah + scattering Fh) (hball : X = Al + scattering Fl)
    (eh el : Vector) (dh dl : UnitSphere)
    (hopth : X = 4 * Real.pi / k * (inner ℂ eh (Fh dh)).im)
    (hoptl : X = 4 * Real.pi / k * (inner ℂ el (Fl dl)).im) :
    0 ≤ |Ah - Al| / X ∧ |Ah - Al| / X < 1 ∧
    |Ah - Al| / X ≤ 1 - k ^ 2 * X / (4 * Real.pi * directivity Fh eh dh) := by
  have hS := positive_scattering Fh hFh hk hX eh dh hopth
  have hd := forward_directivity_floor Fh hFh hk hX eh dh hopth
  have ha : |Ah - Al| = Ah - Al := abs_of_nonneg (sub_nonneg.mpr horder)
  refine ⟨div_nonneg (abs_nonneg _) hX.le, ?_, ?_⟩
  · apply (div_lt_one hX).mpr
    rw [ha]
    linarith
  · have hi : |Ah - Al| / X ≤ 1 - scattering Fh / X := by
      rw [ha]
      apply (div_le_iff₀ hX).mpr
      have he : (1 - scattering Fh / X) * X = X - scattering Fh := by field_simp
      rw [he]
      linarith
    linarith [hd.2]

end CompactMaxwell
