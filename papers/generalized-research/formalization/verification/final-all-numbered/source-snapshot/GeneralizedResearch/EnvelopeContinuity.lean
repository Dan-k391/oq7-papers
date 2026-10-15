import GeneralizedResearch.CanonicalEnvelope
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.MonotoneContinuity

/-! Continuity of the literal implicitly parameterized three-branch envelope,
including both joining points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch
namespace EnvelopeContinuity
open Set

def parameterMap (p : OverlapParameters) (c : Icc (0 : ℝ) p.rho) : Icc (p.rho / 2) p.rho :=
  ⟨middleR p.rho c, by
    have hm := (middleR_strictMonoOn p.rho_pos p.rho_lt_one).monotoneOn
    constructor
    · simpa only [middleR_zero] using hm ⟨le_rfl, p.rho_pos.le⟩ c.property c.property.1
    · simpa only [middleR_rho p.rho_pos p.rho_lt_one] using
        hm c.property ⟨p.rho_pos.le, le_rfl⟩ c.property.2⟩

theorem parameterMap_strictMono (p : OverlapParameters) : StrictMono (parameterMap p) := by
  intro a b hab
  exact middleR_strictMonoOn p.rho_pos p.rho_lt_one a.property b.property hab

theorem parameterMap_surjective (p : OverlapParameters) : Function.Surjective (parameterMap p) := by
  intro r
  have hh : (r : ℝ) ∈ Icc (middleR p.rho 0) (middleR p.rho p.rho) := by
    simpa only [middleR_zero, middleR_rho p.rho_pos p.rho_lt_one] using r.property
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc p.rho_pos.le
    (middleR_continuousOn p.rho_pos p.rho_lt_one) hh
  exact ⟨⟨c, hc⟩, Subtype.ext he⟩

def parameterIso (p : OverlapParameters) : Icc (0 : ℝ) p.rho ≃o Icc (p.rho / 2) p.rho :=
  StrictMono.orderIsoOfSurjective (parameterMap p) (parameterMap_strictMono p)
    (parameterMap_surjective p)

theorem parameterIso_apply (p : OverlapParameters) (c : Icc (0 : ℝ) p.rho) :
    (parameterIso p c : ℝ) = middleR p.rho c := rfl

def parameter (p : OverlapParameters) (r : ℝ) : ℝ :=
  (parameterIso p).symm (projIcc (p.rho / 2) p.rho (by linarith [p.rho_pos]) r)

theorem parameter_mem (p : OverlapParameters) (r : ℝ) : parameter p r ∈ Icc (0 : ℝ) p.rho :=
  ((parameterIso p).symm (projIcc _ _ (by linarith [p.rho_pos]) r)).property

theorem parameter_continuous (p : OverlapParameters) : Continuous (parameter p) :=
  continuous_subtype_val.comp ((parameterIso p).symm.continuous.comp continuous_projIcc)

theorem parameter_equation (p : OverlapParameters) (r : ℝ) (hr : r ∈ Icc (p.rho / 2) p.rho) :
    middleR p.rho (parameter p r) = r := by
  have hh := (parameterIso p).apply_symm_apply (⟨r, hr⟩ : Icc (p.rho / 2) p.rho)
  have hv := congrArg Subtype.val hh
  simpa only [parameter, projIcc_of_mem (by linarith [p.rho_pos]) hr, parameterIso_apply] using hv

theorem parameter_low (p : OverlapParameters) (r : ℝ) (hr : r ≤ p.rho / 2) : parameter p r = 0 := by
  have he : projIcc (p.rho / 2) p.rho (by linarith [p.rho_pos]) r =
      parameterIso p ⟨0, ⟨le_rfl, p.rho_pos.le⟩⟩ := by
    rw [projIcc_of_le_left _ hr]
    apply Subtype.ext
    simp [parameterIso_apply, middleR_zero]
  unfold parameter
  rw [he, OrderIso.symm_apply_apply]

theorem parameter_high (p : OverlapParameters) : parameter p p.rho = p.rho := by
  apply (middleR_strictMonoOn p.rho_pos p.rho_lt_one).injOn
    (parameter_mem p _) ⟨p.rho_pos.le, le_rfl⟩
  rw [parameter_equation p p.rho (by constructor <;> linarith [p.rho_pos]),
    middleR_rho p.rho_pos p.rho_lt_one]

theorem parameter_middle (p : OverlapParameters) (r : ℝ) (hr : p.rho / 2 < r ∧ r < p.rho) :
    parameter p r = (p.middle r hr).c := by
  apply (middleR_strictMonoOn p.rho_pos p.rho_lt_one).injOn
    (parameter_mem p _) ⟨(p.middle r hr).c_pos.le, (p.middle r hr).c_lt_rho.le⟩
  rw [parameter_equation p r ⟨hr.1.le, hr.2.le⟩]
  exact (p.middle_r r hr).symm

def value (p : OverlapParameters) (c : ℝ) : ℝ :=
  p.d * (1 - (c * (p.rho - c) / (2 - p.rho * c - c ^ 2)) ^ 2) * Real.sqrt (1 - c ^ 2)

theorem value_continuousOn (p : OverlapParameters) : ContinuousOn (value p) (Icc 0 p.rho) := by
  unfold value
  apply ContinuousOn.mul
  · apply continuousOn_const.mul
    apply continuousOn_const.sub
    apply ContinuousOn.pow
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro c hc
      exact (closed_denominator_pos p.rho_pos p.rho_lt_one hc.1 hc.2).ne'
  · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)

theorem value_low (p : OverlapParameters) : value p 0 = p.d := by simp [value]

theorem value_high (p : OverlapParameters) : value p p.rho = 1 - p.rho ^ 2 := by
  simp only [value, sub_self, mul_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
  simp only [mul_one]
  change p.d * p.d = _
  nlinarith [p.d_sq]

theorem value_middle (p : OverlapParameters) (r : ℝ) (hr : p.rho / 2 < r ∧ r < p.rho) :
    value p (parameter p r) = 2 * p.d * (p.middle r hr).h := by
  rw [parameter_middle p r hr]
  unfold value MiddleParameters.h MiddleParameters.lambda MiddleParameters.s MiddleParameters.denominator
  change p.d * (1 - ((p.middle r hr).c * (p.rho - (p.middle r hr).c) /
    (2 - p.rho * (p.middle r hr).c - (p.middle r hr).c ^ 2)) ^ 2) *
    Real.sqrt (1 - (p.middle r hr).c ^ 2) =
      2 * p.d * ((1 - ((p.middle r hr).c * (p.rho - (p.middle r hr).c) /
        (2 - p.rho * (p.middle r hr).c - (p.middle r hr).c ^ 2)) ^ 2) *
        Real.sqrt (1 - (p.middle r hr).c ^ 2) / 2)
  ring

theorem envelope_continuous (p : OverlapParameters) : Continuous p.envelope := by
  have hv : Continuous (fun r => value p (parameter p r)) :=
    (value_continuousOn p).comp_continuous (parameter_continuous p) (parameter_mem p)
  have hq : Continuous (fun r : ℝ => 1 - r ^ 2) := by fun_prop
  have hcont := hv.if_le hq continuous_id continuous_const (fun r hr => by
    change r = p.rho at hr
    subst r
    rw [parameter_high, value_high])
  convert hcont using 1
  funext r
  change p.envelope r = if r ≤ p.rho then value p (parameter p r) else 1 - r ^ 2
  by_cases hlo : r ≤ p.rho / 2
  · have hb : r ≤ p.rho := by linarith [p.rho_pos]
    simp only [OverlapParameters.envelope, hlo, hb, ↓reduceDIte, ↓reduceIte]
    rw [parameter_low p r hlo, value_low]
  · by_cases hhi : r < p.rho
    · simp only [OverlapParameters.envelope, hlo, hhi, hhi.le, ↓reduceDIte, ↓reduceIte]
      exact (value_middle p r ⟨lt_of_not_ge hlo, hhi⟩).symm
    · by_cases he : r = p.rho
      · subst r
        simp only [OverlapParameters.envelope, hlo, hhi, le_refl, ↓reduceDIte, ↓reduceIte]
        rw [parameter_high, value_high]
      · have hb : ¬r ≤ p.rho := fun h => he (le_antisymm h (le_of_not_gt hhi))
        simp only [OverlapParameters.envelope, hlo, hhi, hb, ↓reduceDIte, ↓reduceIte]

end EnvelopeContinuity
end GeneralizedResearch
