import OQ7.PhysicalQuarterWave
import OQ7.Transfer

noncomputable section
namespace OQ7
open scoped Matrix Topology
open Filter

/-- The coating matrix in the checkpoint, before its physically harmless scalar sign. -/
def losslessDiagonalScale (ℓ : ℝ) : Mat2 :=
  !![(Real.exp ℓ : ℂ), 0; 0, (Real.exp (-ℓ) : ℂ)]

def coatingIndex₁ (P ℓ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (Real.log P / 4 + ℓ / (2 * (j : ℝ)))

def coatingIndex₂ (P ℓ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (Real.log P / 4 - ℓ / (2 * (j : ℝ)))

def coatingLayers (k P ℓ : ℝ) (j : ℕ) : List HomogeneousLayer :=
  repeatPhysicalLayers (quarterWavePair k (coatingIndex₁ P ℓ j) (coatingIndex₂ P ℓ j)) j

theorem coatingIndex₁_eq_checkpoint {P : ℝ} (hP : 0 < P) (ℓ : ℝ) (j : ℕ) :
    coatingIndex₁ P ℓ j = P ^ (1 / 4 : ℝ) * Real.exp (ℓ / (2 * (j : ℝ))) := by
  rw [coatingIndex₁, Real.exp_add, Real.rpow_def_of_pos hP]
  congr 2
  ring

theorem coatingIndex₂_eq_checkpoint {P : ℝ} (hP : 0 < P) (ℓ : ℝ) (j : ℕ) :
    coatingIndex₂ P ℓ j = P ^ (1 / 4 : ℝ) * Real.exp (-ℓ / (2 * (j : ℝ))) := by
  rw [coatingIndex₂, sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos hP, neg_div]
  congr 2
  ring

theorem losslessDiagonalScale_add (ℓ t : ℝ) :
    losslessDiagonalScale ℓ * losslessDiagonalScale t = losslessDiagonalScale (ℓ + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [losslessDiagonalScale, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add, mul_comm]

theorem losslessDiagonalScale_pow (ℓ : ℝ) (j : ℕ) :
    losslessDiagonalScale ℓ ^ j = losslessDiagonalScale ((j : ℝ) * ℓ) := by
  induction j with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [losslessDiagonalScale]
  | succ j ih =>
    rw [pow_succ, ih, losslessDiagonalScale_add]
    congr 1
    push_cast
    ring

theorem losslessDiagonalScale_det (ℓ : ℝ) : (losslessDiagonalScale ℓ).det = 1 := by
  simp [losslessDiagonalScale, Matrix.det_fin_two, Complex.exp_neg]

theorem losslessDiagonalScale_flux_preserving (ℓ : ℝ) :
    (losslessDiagonalScale ℓ).conjTranspose * fluxForm * losslessDiagonalScale ℓ = fluxForm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [losslessDiagonalScale, fluxForm, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, ← Complex.exp_conj, Complex.exp_neg]

theorem coatingIndex_ratios (P ℓ : ℝ) {j : ℕ} (hj : 0 < j) :
    coatingIndex₁ P ℓ j / coatingIndex₂ P ℓ j = Real.exp (ℓ / (j : ℝ)) ∧
      coatingIndex₂ P ℓ j / coatingIndex₁ P ℓ j = Real.exp (-(ℓ / (j : ℝ))) := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  constructor
  all_goals
    unfold coatingIndex₁ coatingIndex₂
    rw [← Real.exp_sub]
    congr 1
    field_simp
    ring

theorem coatingPair_transfer {k : ℝ} (hk : 0 < k) (P ℓ : ℝ) {j : ℕ} (hj : 0 < j) :
    stackTransfer k (quarterWavePair k (coatingIndex₁ P ℓ j) (coatingIndex₂ P ℓ j)) =
      (-1 : ℂ) • losslessDiagonalScale (ℓ / (j : ℝ)) := by
  have hn₁ : 0 < coatingIndex₁ P ℓ j := Real.exp_pos _
  have hn₂ : 0 < coatingIndex₂ P ℓ j := Real.exp_pos _
  rw [quarterWavePair_transfer hk hn₁ hn₂]
  have hr := coatingIndex_ratios P ℓ hj
  rw [hr.1, hr.2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [losslessDiagonalScale]

/-- A finite sequence of actual lossless layers realizes every nearby coating exactly. -/
theorem coatingLayers_transfer {k : ℝ} (hk : 0 < k) (P ℓ : ℝ) {j : ℕ} (hj : 0 < j) :
    stackTransfer k (coatingLayers k P ℓ j) =
      (-1 : ℂ) ^ j • losslessDiagonalScale ℓ := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  rw [coatingLayers, repeatPhysicalLayers_transfer, coatingPair_transfer hk P ℓ hj,
    smul_pow, losslessDiagonalScale_pow]
  have heq : (j : ℝ) * (ℓ / (j : ℝ)) = ℓ := by field_simp
  rw [heq]

theorem physicallyCoated_transfer {k : ℝ} (hk : 0 < k) (P ℓL ℓR : ℝ)
    {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR) (core : List HomogeneousLayer) :
    stackTransfer k (coatingLayers k P ℓL jL ++ core ++ coatingLayers k P ℓR jR) =
      (-1 : ℂ) ^ (jL + jR) •
        (losslessDiagonalScale ℓR * stackTransfer k core * losslessDiagonalScale ℓL) := by
  rw [stackTransfer_append, stackTransfer_append, coatingLayers_transfer hk P ℓL hjL,
    coatingLayers_transfer hk P ℓR hjR]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_add, Nat.add_comm]
  simp only [mul_assoc]

theorem physicallyCoated_loss (k P ℓL ℓR : ℝ) (jL jR : ℕ) (core : List HomogeneousLayer) :
    integratedLoss (coatingLayers k P ℓL jL ++ core ++ coatingLayers k P ℓR jR) =
      integratedLoss core := by
  simp [integratedLoss_append, coatingLayers, repeatPhysicalLayers_loss, quarterWavePair_loss]

theorem coatingIndex_bounds {P ℓ : ℝ} (hP : 1 < P) {j : ℕ} (hj : 0 < j)
    (hℓ : |ℓ| / (j : ℝ) < Real.log P / 2) :
    1 < coatingIndex₁ P ℓ j ∧ coatingIndex₁ P ℓ j ^ 2 < P ∧
      1 < coatingIndex₂ P ℓ j ∧ coatingIndex₂ P ℓ j ^ 2 < P := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hP0 : 0 < P := by linarith
  have hr := (div_lt_iff₀ hj').mp hℓ
  have hden : 0 < 2 * (j : ℝ) := by positivity
  have hhi : ℓ / (2 * (j : ℝ)) < Real.log P / 4 :=
    (div_lt_iff₀ hden).mpr (by nlinarith [le_abs_self ℓ])
  have hlo : -(Real.log P / 4) < ℓ / (2 * (j : ℝ)) :=
    (lt_div_iff₀ hden).mpr (by nlinarith [neg_abs_le ℓ])
  have he₁ : 0 < Real.log P / 4 + ℓ / (2 * (j : ℝ)) := by linarith
  have he₂ : 0 < Real.log P / 4 - ℓ / (2 * (j : ℝ)) := by linarith
  refine ⟨Real.one_lt_exp_iff.mpr he₁, ?_, Real.one_lt_exp_iff.mpr he₂, ?_⟩
  all_goals
    dsimp only [coatingIndex₁, coatingIndex₂]
    rw [← Real.exp_nat_mul]
    calc
      _ < Real.exp (Real.log P) := Real.exp_lt_exp.mpr (by norm_num; linarith)
      _ = P := Real.exp_log hP0

theorem coatingLayers_admissible {k P Q ℓ : ℝ} (hk : 0 < k) (hP : 1 < P) (hQ : 0 ≤ Q)
    {j : ℕ} (hj : 0 < j) (hℓ : |ℓ| / (j : ℝ) < Real.log P / 2) :
    StackAdmissible P Q (coatingLayers k P ℓ j) := by
  have hb := coatingIndex_bounds hP hj hℓ
  apply repeatPhysicalLayers_admissible
  intro layer hm
  simp only [quarterWavePair, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · exact quarterWaveLayer_admissible hk hb.1.le hb.2.1.le hQ
  · exact quarterWaveLayer_admissible hk hb.2.2.1.le hb.2.2.2.le hQ

theorem coatingLayers_loss (k P ℓ : ℝ) (j : ℕ) :
    integratedLoss (coatingLayers k P ℓ j) = 0 := by
  rw [coatingLayers, repeatPhysicalLayers_loss, quarterWavePair_loss, mul_zero]

theorem coatingLayers_thickness (k P ℓ : ℝ) (j : ℕ) :
    totalThickness (coatingLayers k P ℓ j) =
      (j : ℝ) * (Real.pi / (2 * k) *
        (1 / coatingIndex₁ P ℓ j + 1 / coatingIndex₂ P ℓ j)) := by
  rw [coatingLayers, repeatPhysicalLayers_thickness, quarterWavePair_thickness]

theorem coatingLayers_thickness_lt {k P ℓ : ℝ} (hk : 0 < k) (hP : 1 < P)
    {j : ℕ} (hj : 0 < j) (hℓ : |ℓ| / (j : ℝ) < Real.log P / 2) :
    totalThickness (coatingLayers k P ℓ j) < (j : ℝ) * Real.pi / k := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hb := coatingIndex_bounds hP hj hℓ
  rw [coatingLayers, repeatPhysicalLayers_thickness]
  have hp := quarterWavePair_thickness_lt hk hb.1 hb.2.2.1
  simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hp hj'

theorem physicallyCoated_thickness_lt {k P ℓL ℓR : ℝ} (hk : 0 < k) (hP : 1 < P)
    {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR)
    (hℓL : |ℓL| / (jL : ℝ) < Real.log P / 2)
    (hℓR : |ℓR| / (jR : ℝ) < Real.log P / 2) (core : List HomogeneousLayer) :
    totalThickness (coatingLayers k P ℓL jL ++ core ++ coatingLayers k P ℓR jR) <
      totalThickness core + ((jL + jR : ℕ) : ℝ) * Real.pi / k := by
  have hL := coatingLayers_thickness_lt hk hP hjL hℓL
  have hR := coatingLayers_thickness_lt hk hP hjR hℓR
  simp only [totalThickness_append, Nat.cast_add, add_mul, add_div]
  linarith

theorem exists_coatingPairCount {P : ℝ} (hP : 1 < P) (ℓ₀ : ℝ) :
    ∃ j : ℕ, 0 < j ∧ |ℓ₀| / (j : ℝ) < Real.log P / 2 := by
  have hlog : 0 < Real.log P := Real.log_pos hP
  obtain ⟨j, hj⟩ := exists_nat_gt (max 1 (2 * |ℓ₀| / Real.log P))
  have hj' : (0 : ℝ) < j := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hj)
  have hdiv := (le_max_right (1 : ℝ) (2 * |ℓ₀| / Real.log P)).trans_lt hj
  refine ⟨j, by exact_mod_cast hj', (div_lt_iff₀ hj').mpr ?_⟩
  have hm := (div_lt_iff₀ hlog).mp hdiv
  nlinarith

theorem coatingLayers_eventually_physical {k P Q ℓ₀ : ℝ} (hk : 0 < k) (hP : 1 < P)
    (hQ : 0 ≤ Q) {j : ℕ} (hj : 0 < j) (hℓ₀ : |ℓ₀| / (j : ℝ) < Real.log P / 2) :
    ∀ᶠ ℓ : ℝ in 𝓝 ℓ₀, StackAdmissible P Q (coatingLayers k P ℓ j) ∧
      totalThickness (coatingLayers k P ℓ j) < (j : ℝ) * Real.pi / k := by
  have hc : Continuous (fun ℓ : ℝ => |ℓ| / (j : ℝ)) := continuous_abs.div_const _
  filter_upwards [(hc.tendsto ℓ₀).eventually (eventually_lt_nhds hℓ₀)] with ℓ hℓ
  exact ⟨coatingLayers_admissible hk hP hQ hj hℓ, coatingLayers_thickness_lt hk hP hj hℓ⟩

/-- The checkpoint's fixed-pair-count physical family, with exact transfer and uniform geometry. -/
theorem exists_physical_coating_family {k P Q : ℝ} (hk : 0 < k) (hP : 1 < P)
    (hQ : 0 ≤ Q) (ℓ₀ : ℝ) :
    ∃ j : ℕ, 0 < j ∧ ∀ᶠ ℓ : ℝ in 𝓝 ℓ₀,
      StackAdmissible P Q (coatingLayers k P ℓ j) ∧
      stackTransfer k (coatingLayers k P ℓ j) = (-1 : ℂ) ^ j • losslessDiagonalScale ℓ ∧
      integratedLoss (coatingLayers k P ℓ j) = 0 ∧
      totalThickness (coatingLayers k P ℓ j) < (j : ℝ) * Real.pi / k := by
  obtain ⟨j, hj, hℓ₀⟩ := exists_coatingPairCount hP ℓ₀
  refine ⟨j, hj, ?_⟩
  filter_upwards [coatingLayers_eventually_physical hk hP hQ hj hℓ₀] with ℓ hℓ
  exact ⟨hℓ.1, coatingLayers_transfer hk P ℓ hj, coatingLayers_loss k P ℓ j, hℓ.2⟩

#print axioms coatingIndex₁_eq_checkpoint
#print axioms coatingIndex₂_eq_checkpoint
#print axioms losslessDiagonalScale_add
#print axioms losslessDiagonalScale_pow
#print axioms losslessDiagonalScale_det
#print axioms losslessDiagonalScale_flux_preserving
#print axioms coatingIndex_ratios
#print axioms coatingPair_transfer
#print axioms coatingLayers_transfer
#print axioms physicallyCoated_transfer
#print axioms physicallyCoated_loss
#print axioms coatingIndex_bounds
#print axioms coatingLayers_admissible
#print axioms coatingLayers_loss
#print axioms coatingLayers_thickness
#print axioms coatingLayers_thickness_lt
#print axioms physicallyCoated_thickness_lt
#print axioms exists_coatingPairCount
#print axioms coatingLayers_eventually_physical
#print axioms exists_physical_coating_family
end OQ7
