import OQ7.SharpPhysicalConstruction
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

/-! Original generalized-manuscript Corollary 5.2. The infimum is taken over
actual finite homogeneous dielectric stacks, retaining every exact material and
power constraint of `OQ7.exactTargetClass`. Neither an attained supremum nor an
attained minimum thickness is assumed. The only asymptotic input is the proved
unconditional physical theorem `OQ7.theorem51`. -/

noncomputable section
namespace GeneralizedResearch
open OQ7 Filter Set
open scoped Topology

def nearOptimalStacks (p : PhysicalParameters) (η : ℝ) : Set (List HomogeneousLayer) :=
  {layers | layers ∈ exactTargetClass p (totalThickness layers) ∧
    ScalarEnvelope.D0 p.T p.a - η ≤ stackAsymmetry p.k layers}

def nearOptimalThicknesses (p : PhysicalParameters) (η : ℝ) : Set ℝ :=
  totalThickness '' nearOptimalStacks p η

def minimumThickness (p : PhysicalParameters) (η : ℝ) : ℝ :=
  sInf (nearOptimalThicknesses p η)

theorem exactTargetClass_mono {p : PhysicalParameters} {L L' : ℝ}
    (hLL' : L ≤ L') {layers : List HomogeneousLayer}
    (hm : layers ∈ exactTargetClass p L) : layers ∈ exactTargetClass p L' :=
  ⟨hm.1, hm.2.1, hm.2.2.1.trans hLL', hm.2.2.2.1, hm.2.2.2.2⟩

theorem exactTargetClass_at_own_thickness {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    layers ∈ exactTargetClass p (totalThickness layers) :=
  ⟨hm.1, hm.2.1, le_rfl, hm.2.2.2.1, hm.2.2.2.2⟩

theorem nearOptimalThicknesses_bddBelow (p : PhysicalParameters) (η : ℝ) :
    BddBelow (nearOptimalThicknesses p η) := by
  refine ⟨0, ?_⟩
  rintro w ⟨layers, hm, rfl⟩
  exact totalThickness_nonneg hm.1.1

/-- Strict proximity of the supremum supplies a genuine near-optimal stack. -/
theorem nearOptimal_exists_of_optimal_deficit_lt {p : PhysicalParameters} {η L : ℝ}
    (hne : (exactTargetClass p L).Nonempty)
    (hgap : ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L < η) :
    ∃ layers ∈ nearOptimalStacks p η, totalThickness layers ≤ L := by
  have hsup : ScalarEnvelope.D0 p.T p.a - η <
      sSup (stackAsymmetry p.k '' exactTargetClass p L) := by
    change ScalarEnvelope.D0 p.T p.a - η < optimalAsymmetry p L
    linarith
  obtain ⟨d, ⟨layers, hm, rfl⟩, hd⟩ :=
    exists_lt_of_lt_csSup (hne.image (stackAsymmetry p.k)) hsup
  exact ⟨layers, ⟨exactTargetClass_at_own_thickness hm, hd.le⟩, hm.2.2.1⟩

theorem minimumThickness_le_of_optimal_deficit_lt {p : PhysicalParameters} {η L : ℝ}
    (hne : (exactTargetClass p L).Nonempty)
    (hgap : ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L < η) :
    (nearOptimalThicknesses p η).Nonempty ∧ minimumThickness p η ≤ L := by
  obtain ⟨layers, hm, hw⟩ := nearOptimal_exists_of_optimal_deficit_lt hne hgap
  have hmem : totalThickness layers ∈ nearOptimalThicknesses p η := ⟨layers, hm, rfl⟩
  exact ⟨⟨_, hmem⟩, (csInf_le (nearOptimalThicknesses_bddBelow p η) hmem).trans hw⟩

theorem budget_le_minimumThickness_of_optimal_deficit_gt
    {p : PhysicalParameters} {η L : ℝ}
    (hne : (nearOptimalThicknesses p η).Nonempty)
    (hgap : η < ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L) :
    L ≤ minimumThickness p η := by
  apply le_csInf hne
  rintro w ⟨layers, hm, rfl⟩
  by_contra hw
  have hbudget : layers ∈ exactTargetClass p L :=
    exactTargetClass_mono (le_of_not_ge hw) hm.1
  have hbound := stackAsymmetry_le_optimal hbudget
  linarith [hm.2]

theorem minimumThickness_nonneg {p : PhysicalParameters} {η : ℝ}
    (hne : (nearOptimalThicknesses p η).Nonempty) : 0 ≤ minimumThickness p η := by
  apply le_csInf hne
  rintro w ⟨layers, hm, rfl⟩
  exact totalThickness_nonneg hm.1.1

theorem asymptoticCoefficient_pos (p : PhysicalParameters) : 0 < asymptoticCoefficient p := by
  have hα := (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  have hk := p.k_pos
  have hM := p.M_pos
  have hQ := p.Q_pos
  unfold asymptoticCoefficient
  positivity

/-- A test budget at a chosen normalized thickness `r`. -/
def inverseBudget (p : PhysicalParameters) (r η : ℝ) : ℝ := r / (p.k * Real.sqrt η)

theorem inverseBudget_tendsto_atTop (p : PhysicalParameters) {r : ℝ} (hr : 0 < r) :
    Tendsto (inverseBudget p r) (𝓝[>] (0 : ℝ)) atTop := by
  have h := Tendsto.const_mul_atTop' (div_pos hr p.k_pos)
    (Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero)
  convert h using 1
  funext η
  simp [inverseBudget, Real.sqrt_inv, div_eq_mul_inv, mul_assoc, mul_comm]

theorem inverseBudget_normalized (p : PhysicalParameters) (r : ℝ) {η : ℝ}
    (hη : 0 < η) : p.k * inverseBudget p r η * Real.sqrt η = r := by
  have hk : p.k ≠ 0 := p.k_pos.ne'
  have hs : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  unfold inverseBudget
  field_simp

theorem inverseBudget_scaled (p : PhysicalParameters) (r : ℝ) {η : ℝ}
    (hη : 0 < η) : (p.k * inverseBudget p r η) ^ 2 * η = r ^ 2 := by
  have h := congrArg (fun x : ℝ => x ^ 2) (inverseBudget_normalized p r hη)
  simpa only [mul_pow, Real.sq_sqrt hη.le] using h

theorem minimumThickness_eventually_upper (p : PhysicalParameters) {r : ℝ}
    (hr : Real.sqrt (asymptoticCoefficient p) < r) :
    ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), (nearOptimalThicknesses p η).Nonempty ∧
      p.k * minimumThickness p η * Real.sqrt η ≤ r := by
  have hC := asymptoticCoefficient_pos p
  have hRoot : 0 < Real.sqrt (asymptoticCoefficient p) := Real.sqrt_pos.mpr hC
  have hr0 : 0 < r := hRoot.trans hr
  have hr2 : asymptoticCoefficient p < r ^ 2 := by
    nlinarith [Real.sq_sqrt hC.le]
  have hbud := inverseBudget_tendsto_atTop p hr0
  have hth := theorem51 p
  have hscale := hth.2.2.comp hbud
  filter_upwards [hbud.eventually hth.1,
    hscale.eventually (eventually_lt_nhds hr2), self_mem_nhdsWithin] with η hne hs hη
  have hη0 : 0 < η := hη
  have htest := inverseBudget_scaled p r hη0
  have hfactor : 0 < (p.k * inverseBudget p r η) ^ 2 := by
    apply sq_pos_of_pos
    exact mul_pos p.k_pos (div_pos hr0 (mul_pos p.k_pos (Real.sqrt_pos.mpr hη0)))
  have hgap : ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p (inverseBudget p r η) < η := by
    change (p.k * inverseBudget p r η) ^ 2 *
      (ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p (inverseBudget p r η)) < r ^ 2 at hs
    apply (mul_lt_mul_iff_right₀ hfactor).mp
    rw [htest]
    exact hs
  obtain ⟨hne', hle⟩ := minimumThickness_le_of_optimal_deficit_lt hne hgap
  refine ⟨hne', ?_⟩
  calc p.k * minimumThickness p η * Real.sqrt η
      ≤ p.k * inverseBudget p r η * Real.sqrt η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle p.k_pos.le)
          (Real.sqrt_nonneg η)
    _ = r := inverseBudget_normalized p r hη0

theorem minimumThickness_eventually_nonempty (p : PhysicalParameters) :
    ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), (nearOptimalThicknesses p η).Nonempty :=
  (minimumThickness_eventually_upper p (lt_add_one _)).mono (fun _ h => h.1)

/-- Every positive accuracy tolerance has a finite physical candidate. -/
theorem nearOptimalThicknesses_nonempty (p : PhysicalParameters) {η : ℝ} (hη : 0 < η) :
    (nearOptimalThicknesses p η).Nonempty := by
  have he : ∀ᶠ η' : ℝ in 𝓝[>] (0 : ℝ),
      (nearOptimalThicknesses p η').Nonempty ∧ 0 < η' ∧ η' < η := by
    filter_upwards [minimumThickness_eventually_nonempty p,
      (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with η' hne hlt hpos
    exact ⟨hne, hpos, hlt⟩
  obtain ⟨η', ⟨w, layers, hm, rfl⟩, _, hlt⟩ := he.exists
  refine ⟨totalThickness layers, layers, ⟨hm.1, ?_⟩, rfl⟩
  linarith [hm.2]

theorem minimumThickness_eventually_lower (p : PhysicalParameters) {r : ℝ}
    (hr0 : 0 < r) (hr : r < Real.sqrt (asymptoticCoefficient p)) :
    ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), r ≤ p.k * minimumThickness p η * Real.sqrt η := by
  have hC := asymptoticCoefficient_pos p
  have hr2 : r ^ 2 < asymptoticCoefficient p := by
    nlinarith [Real.sq_sqrt hC.le]
  have hbud := inverseBudget_tendsto_atTop p hr0
  have hscale := (theorem51 p).2.2.comp hbud
  filter_upwards [minimumThickness_eventually_nonempty p,
    hscale.eventually (eventually_gt_nhds hr2), self_mem_nhdsWithin] with η hne hs hη
  have hη0 : 0 < η := hη
  have htest := inverseBudget_scaled p r hη0
  have hfactor : 0 < (p.k * inverseBudget p r η) ^ 2 := by
    apply sq_pos_of_pos
    exact mul_pos p.k_pos (div_pos hr0 (mul_pos p.k_pos (Real.sqrt_pos.mpr hη0)))
  have hgap : η < ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p (inverseBudget p r η) := by
    change r ^ 2 < (p.k * inverseBudget p r η) ^ 2 *
      (ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p (inverseBudget p r η)) at hs
    apply (mul_lt_mul_iff_right₀ hfactor).mp
    rw [htest]
    exact hs
  have hle := budget_le_minimumThickness_of_optimal_deficit_gt hne hgap
  calc r = p.k * inverseBudget p r η * Real.sqrt η :=
      (inverseBudget_normalized p r hη0).symm
    _ ≤ p.k * minimumThickness p η * Real.sqrt η :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle p.k_pos.le)
        (Real.sqrt_nonneg η)

/-- The infimum of admissible near-optimal thicknesses diverges. -/
theorem minimumThickness_tendsto_atTop (p : PhysicalParameters) :
    Tendsto (minimumThickness p) (𝓝[>] (0 : ℝ)) atTop := by
  let r := Real.sqrt (asymptoticCoefficient p) / 2
  have hRoot := Real.sqrt_pos.mpr (asymptoticCoefficient_pos p)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr : r < Real.sqrt (asymptoticCoefficient p) := by dsimp [r]; linarith
  have hcomp : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), inverseBudget p r η ≤ minimumThickness p η := by
    filter_upwards [minimumThickness_eventually_lower p hr0 hr,
      self_mem_nhdsWithin] with η hη hpos
    have hp : 0 < p.k * Real.sqrt η := mul_pos p.k_pos (Real.sqrt_pos.mpr hpos)
    have hb := inverseBudget_normalized p r hpos
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith
  exact tendsto_atTop_mono' _ hcomp (inverseBudget_tendsto_atTop p hr0)

/-- Corollary 5.2, in normalized limit form. The leading coefficient is positive,
so this is equivalent to the manuscript's asymptotic equivalence. -/
theorem corollary52 (p : PhysicalParameters) :
    Tendsto (fun η : ℝ => p.k * minimumThickness p η * Real.sqrt η)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (asymptoticCoefficient p))) := by
  have hRoot : 0 < Real.sqrt (asymptoticCoefficient p) :=
    Real.sqrt_pos.mpr (asymptoticCoefficient_pos p)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, har, hr⟩ := exists_between (max_lt hRoot ha)
    have hr0 : 0 < r := (le_max_left 0 a).trans_lt har
    have har' : a < r := (le_max_right 0 a).trans_lt har
    exact (minimumThickness_eventually_lower p hr0 hr).mono (fun _ h => har'.trans_le h)
  · intro b hb
    obtain ⟨r, hr, hrb⟩ := exists_between hb
    exact (minimumThickness_eventually_upper p hr).mono (fun _ h => h.2.trans_lt hrb)

/-- Exact leading constant printed in equation (43). -/
def minimumThicknessLeadingCoefficient (p : PhysicalParameters) : ℝ :=
  Real.pi * (p.k * p.M) ^ 2 / p.Q * Real.sqrt (ScalarEnvelope.alpha p.T p.a / (3 * p.P))

theorem minimumThicknessLeadingCoefficient_eq (p : PhysicalParameters) :
    minimumThicknessLeadingCoefficient p = Real.sqrt (asymptoticCoefficient p) := by
  have hα := (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  have hc : 0 ≤ ScalarEnvelope.alpha p.T p.a / (3 * p.P) := by positivity
  have hs : (minimumThicknessLeadingCoefficient p) ^ 2 = asymptoticCoefficient p := by
    unfold minimumThicknessLeadingCoefficient asymptoticCoefficient
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hc]
    have hQ := p.Q_pos.ne'
    have hPn := hP.ne'
    field_simp
  have hnonneg : 0 ≤ minimumThicknessLeadingCoefficient p := by
    unfold minimumThicknessLeadingCoefficient
    exact mul_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) p.Q_pos.le)
      (Real.sqrt_nonneg _)
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

/-- Exact asymptotic ratio, without a claim that the infimum is attained. -/
theorem corollary52_ratio (p : PhysicalParameters) :
    Tendsto (fun η : ℝ => p.k * minimumThickness p η /
      (minimumThicknessLeadingCoefficient p / Real.sqrt η))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hc : minimumThicknessLeadingCoefficient p ≠ 0 := by
    rw [minimumThicknessLeadingCoefficient_eq]
    exact (Real.sqrt_pos.mpr (asymptoticCoefficient_pos p)).ne'
  have ht := (corollary52 p).div_const (minimumThicknessLeadingCoefficient p)
  rw [← minimumThicknessLeadingCoefficient_eq, div_self hc] at ht
  convert ht using 1
  funext η
  rw [div_div_eq_mul_div]

/-- The denominator is exactly the expression in the original equation (43). -/
theorem corollary52_original_ratio (p : PhysicalParameters) :
    Tendsto (fun η : ℝ => p.k * minimumThickness p η /
      (Real.pi * (p.k * p.M) ^ 2 / p.Q *
        Real.sqrt (ScalarEnvelope.alpha p.T p.a / (3 * p.P * η))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hα := (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  have ha : 0 ≤ ScalarEnvelope.alpha p.T p.a / (3 * p.P) := by positivity
  convert corollary52_ratio p using 1
  funext η
  congr 1
  rw [div_mul_eq_div_div, Real.sqrt_div ha]
  unfold minimumThicknessLeadingCoefficient
  ring

end GeneralizedResearch

#print axioms GeneralizedResearch.corollary52
#print axioms GeneralizedResearch.corollary52_ratio
#print axioms GeneralizedResearch.corollary52_original_ratio
#print axioms GeneralizedResearch.nearOptimalThicknesses_nonempty
#print axioms GeneralizedResearch.minimumThickness_tendsto_atTop
