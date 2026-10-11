import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

def setSupportedL2 (μ : Measure α) (s : Set α) : Submodule ℂ (Lp E 2 μ) where
  carrier := {f | ∀ᵐ x ∂μ, x ∉ s → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := μ)] with x hx
    exact fun _ => hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx hx
    intro hxs
    rw [hx]
    change f x + g x = 0
    rw [hfx hxs, hgx hxs, add_zero]
  smul_mem' := by
    intro z f hf
    filter_upwards [hf, Lp.coeFn_smul z f] with x hfx hx
    intro hxs
    rw [hx]
    change z • f x = 0
    rw [hfx hxs, smul_zero]

abbrev SetSupportedL2 (μ : Measure α) (s : Set α) := setSupportedL2 (E := E) μ s

def indicatorL2 (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) : Lp E 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator (fun x => f x))

theorem indicatorL2_coe (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    indicatorL2 μ s hs f =ᵐ[μ] s.indicator (fun x => f x) :=
  ((Lp.memLp f).indicator hs).coeFn_toLp

theorem indicatorL2_supported (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    indicatorL2 μ s hs f ∈ setSupportedL2 μ s := by
  filter_upwards [indicatorL2_coe μ s hs f] with x hx
  intro hxs
  rw [hx, indicator_of_notMem hxs]

theorem indicatorL2_norm_le (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    ‖indicatorL2 μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [indicatorL2_coe μ s hs f] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self (s := s) (fun x => f x) x

theorem indicatorL2_add (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f g : Lp E 2 μ) :
    indicatorL2 μ s hs (f + g) = indicatorL2 μ s hs f + indicatorL2 μ s hs g := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ s hs (f + g), indicatorL2_coe μ s hs f,
    indicatorL2_coe μ s hs g, Lp.coeFn_add f g,
    Lp.coeFn_add (indicatorL2 μ s hs f) (indicatorL2 μ s hs g)] with x hfg hf hg ha hb
  rw [hfg, hb]
  change s.indicator (fun y => (f + g) y) x = indicatorL2 μ s hs f x + indicatorL2 μ s hs g x
  rw [hf, hg]
  by_cases hx : x ∈ s
  · simpa only [indicator_of_mem hx, Pi.add_apply] using ha
  · simp only [indicator_of_notMem hx, add_zero]

theorem indicatorL2_smul (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (z : ℂ) (f : Lp E 2 μ) :
    indicatorL2 μ s hs (z • f) = z • indicatorL2 μ s hs f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ s hs (z • f), indicatorL2_coe μ s hs f,
    Lp.coeFn_smul z f, Lp.coeFn_smul z (indicatorL2 μ s hs f)] with x hzf hf ha hb
  rw [hzf, hb]
  change s.indicator (fun y => (z • f) y) x = z • indicatorL2 μ s hs f x
  rw [hf]
  by_cases hx : x ∈ s
  · simpa only [indicator_of_mem hx, Pi.smul_apply] using ha
  · simp only [indicator_of_notMem hx, smul_zero]

def setRestrictionLinear (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    Lp E 2 μ →ₗ[ℂ] SetSupportedL2 (E := E) μ s where
  toFun f := ⟨indicatorL2 μ s hs f, indicatorL2_supported μ s hs f⟩
  map_add' f g := Subtype.ext (indicatorL2_add μ s hs f g)
  map_smul' z f := Subtype.ext (indicatorL2_smul μ s hs z f)

def setRestrictionCLM (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    Lp E 2 μ →L[ℂ] SetSupportedL2 (E := E) μ s :=
  (setRestrictionLinear (E := E) μ s hs).mkContinuous 1 fun f => by
    change ‖indicatorL2 μ s hs f‖ ≤ 1 * ‖f‖
    simpa using indicatorL2_norm_le μ s hs f

theorem setRestrictionCLM_norm_le (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    ‖setRestrictionCLM (E := E) μ s hs‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem indicatorL2_eq_self_iff (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    indicatorL2 μ s hs f = f ↔ f ∈ setSupportedL2 μ s := by
  constructor
  · intro h
    rw [← h]
    exact indicatorL2_supported μ s hs f
  · intro hf
    apply Lp.ext
    filter_upwards [indicatorL2_coe μ s hs f, hf] with x hx hz
    rw [hx]
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs, hz hxs]

theorem setSupportedL2_isClosed (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    IsClosed (setSupportedL2 (E := E) μ s : Set (Lp E 2 μ)) := by
  have he : (setSupportedL2 (E := E) μ s : Set (Lp E 2 μ)) =
      {f : Lp E 2 μ | (setSupportedL2 (E := E) μ s).subtypeL (setRestrictionCLM μ s hs f) = f} := by
    ext f
    change f ∈ setSupportedL2 μ s ↔ indicatorL2 μ s hs f = f
    exact (indicatorL2_eq_self_iff μ s hs f).symm
  rw [he]
  exact isClosed_eq
    ((setSupportedL2 (E := E) μ s).subtypeL.continuous.comp (setRestrictionCLM μ s hs).continuous) continuous_id

theorem setRestrictionCLM_inner (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (f : SetSupportedL2 (E := E) μ s) (g : Lp E 2 μ) :
    inner ℂ (f : Lp E 2 μ) (setRestrictionCLM μ s hs g : Lp E 2 μ) = inner ℂ (f : Lp E 2 μ) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ s hs g, f.property] with x hx hf
  change inner ℂ ((f : Lp E 2 μ) x) ((indicatorL2 μ s hs g) x) = _
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs, hf hxs]
    simp

end OQ7Prescribed
