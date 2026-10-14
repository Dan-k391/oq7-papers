import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def slabProductRegion (r L : ℝ) : Set (ℂ × ℝ) := Metric.closedBall 0 r ×ˢ Icc 0 L

theorem slabProductRegion_measurable (r L : ℝ) : MeasurableSet (slabProductRegion r L) :=
  Metric.isClosed_closedBall.measurableSet.prod measurableSet_Icc

theorem slabProductRegion_volume_real (r L : ℝ) (hr : 0 ≤ r) (hL : 0 ≤ L) :
    (volume (slabProductRegion r L)).toReal = r ^ 2 * Real.pi * L := by
  rw [slabProductRegion, Measure.volume_eq_prod, Measure.prod_prod,
    Complex.volume_closedBall, Real.volume_Icc]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal hL]

theorem slabProductRegion_measure_lt_top (r L : ℝ) : volume (slabProductRegion r L) < ⊤ :=
  ((isCompact_closedBall (0 : ℂ) r).prod isCompact_Icc).measure_lt_top

theorem slabProduct_uniform_error_integral_sq (f : ℂ × ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) (D X L R : ℝ)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hL : 0 ≤ L) (hR : 0 < R)
    (hb : ∀ᵐ y : ℂ × ℝ ∂volume, y ∈ slabProductRegion (X * R) L → ‖f y‖ ≤ D / R) :
    (∫ y in slabProductRegion (X * R) L, ‖f y‖ ^ 2) ≤ D ^ 2 * X ^ 2 * Real.pi * L := by
  let S := slabProductRegion (X * R) L
  have hm := slabProductRegion_measurable (X * R) L
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr (slabProductRegion_measure_lt_top (X * R) L).ne
  have hrb : ∀ᵐ y : ℂ × ℝ ∂volume.restrict S, ‖f y‖ ≤ D / R := by
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem hm] with y hy hs
    exact hy hs
  have hfr : AEStronglyMeasurable f (volume.restrict S) := hf.mono_measure Measure.restrict_le_self
  have hmem : MemLp f 2 (volume.restrict S) := MemLp.of_bound hfr (D / R) hrb
  have hfi := (memLp_two_iff_integrable_sq_norm hfr).1 hmem
  have he := integral_mono_ae hfi (integrable_const ((D / R) ^ 2))
    (hrb.mono fun y hy => by nlinarith [norm_nonneg (f y), div_nonneg hD hR.le])
  rw [integral_const, smul_eq_mul] at he
  change (∫ y in S, ‖f y‖ ^ 2) ≤ ((volume.restrict S) univ).toReal * (D / R) ^ 2 at he
  rw [Measure.restrict_apply_univ] at he
  change (∫ y in slabProductRegion (X * R) L, ‖f y‖ ^ 2) ≤
    (volume (slabProductRegion (X * R) L)).toReal * (D / R) ^ 2 at he
  rw [slabProductRegion_volume_real (X * R) L (mul_nonneg hX hR.le) hL] at he
  have hc : (X * R) ^ 2 * Real.pi * L * (D / R) ^ 2 = D ^ 2 * X ^ 2 * Real.pi * L := by
    field_simp [hR.ne']
    <;> ring
  exact he.trans_eq hc

end OQ7Prescribed
