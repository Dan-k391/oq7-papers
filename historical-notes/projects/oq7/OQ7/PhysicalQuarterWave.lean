import OQ7.Layers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace OQ7
open scoped Matrix ComplexOrder

/-- An actual lossless quarter-wave layer, parameterized by its positive real index. -/
def quarterWaveLayer (k n : ℝ) : HomogeneousLayer :=
  ⟨n ^ 2, 0, Real.pi / (2 * k * n)⟩

theorem refractiveIndex_quarterWave (k : ℝ) {n : ℝ} (hn : 0 ≤ n) :
    refractiveIndex (quarterWaveLayer k n) = (n : ℂ) := by
  unfold refractiveIndex relativePermittivity quarterWaveLayer
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg n)]
  simp only [Complex.ofReal_re, Real.sqrt_sq hn]

theorem layerTransfer_quarterWave {k n : ℝ} (hk : 0 < k) (hn : 0 < n) :
    layerTransfer k (quarterWaveLayer k n) =
      (!![0, Complex.I / (n : ℂ); Complex.I * (n : ℂ), 0] : Mat2) := by
  rw [layerTransfer, refractiveIndex_quarterWave k hn.le]
  have hθ : (k : ℂ) * (n : ℂ) * ((quarterWaveLayer k n).width : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) := by
    dsimp [quarterWaveLayer]
    push_cast
    field_simp
  simp only [homogeneousTransfer, hθ, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero, Complex.ofReal_one,
    mul_one]

theorem quarterWaveLayer_admissible {k n P Q : ℝ} (hk : 0 < k) (hn : 1 ≤ n)
    (hP : n ^ 2 ≤ P) (hQ : 0 ≤ Q) : LayerAdmissible P Q (quarterWaveLayer k n) := by
  have hn0 : 0 < n := by linarith
  refine ⟨by dsimp [quarterWaveLayer]; nlinarith, hP, le_rfl, hQ, ?_⟩
  exact div_nonneg Real.pi_pos.le (by positivity)

def quarterWavePair (k n₁ n₂ : ℝ) : List HomogeneousLayer :=
  [quarterWaveLayer k n₁, quarterWaveLayer k n₂]

theorem quarterWavePair_transfer {k n₁ n₂ : ℝ} (hk : 0 < k)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    stackTransfer k (quarterWavePair k n₁ n₂) =
      (!![-((n₁ / n₂ : ℝ) : ℂ), 0; 0, -((n₂ / n₁ : ℝ) : ℂ)] : Mat2) := by
  simp only [quarterWavePair, stackTransfer, one_mul, layerTransfer_quarterWave hk hn₁,
    layerTransfer_quarterWave hk hn₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals push_cast; field_simp; ring_nf; simp [Complex.I_sq]

theorem stackTransfer_append (k : ℝ) (left right : List HomogeneousLayer) :
    stackTransfer k (left ++ right) = stackTransfer k right * stackTransfer k left := by
  induction left with
  | nil => simp [stackTransfer]
  | cons layer layers ih => simp only [List.cons_append, stackTransfer, ih, mul_assoc]

theorem totalThickness_append (left right : List HomogeneousLayer) :
    totalThickness (left ++ right) = totalThickness left + totalThickness right := by
  simp [totalThickness]

theorem integratedLoss_append (left right : List HomogeneousLayer) :
    integratedLoss (left ++ right) = integratedLoss left + integratedLoss right := by
  simp [integratedLoss]

def repeatPhysicalLayers (layers : List HomogeneousLayer) (j : ℕ) : List HomogeneousLayer :=
  (List.replicate j layers).flatten

theorem repeatPhysicalLayers_transfer (k : ℝ) (layers : List HomogeneousLayer) (j : ℕ) :
    stackTransfer k (repeatPhysicalLayers layers j) = stackTransfer k layers ^ j := by
  induction j with
  | zero => simp [repeatPhysicalLayers, stackTransfer]
  | succ j ih =>
    simp only [repeatPhysicalLayers, List.replicate_succ, List.flatten_cons,
      stackTransfer_append] at *
    rw [ih, pow_succ]

theorem repeatPhysicalLayers_thickness (layers : List HomogeneousLayer) (j : ℕ) :
    totalThickness (repeatPhysicalLayers layers j) = (j : ℝ) * totalThickness layers := by
  induction j with
  | zero => simp [repeatPhysicalLayers, totalThickness]
  | succ j ih =>
    simp only [repeatPhysicalLayers, List.replicate_succ, List.flatten_cons,
      totalThickness_append] at *
    rw [ih, Nat.cast_add_one]
    ring

theorem repeatPhysicalLayers_loss (layers : List HomogeneousLayer) (j : ℕ) :
    integratedLoss (repeatPhysicalLayers layers j) = (j : ℝ) * integratedLoss layers := by
  induction j with
  | zero => simp [repeatPhysicalLayers, integratedLoss]
  | succ j ih =>
    simp only [repeatPhysicalLayers, List.replicate_succ, List.flatten_cons,
      integratedLoss_append] at *
    rw [ih, Nat.cast_add_one]
    ring

theorem repeatPhysicalLayers_admissible {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (j : ℕ) :
    StackAdmissible P Q (repeatPhysicalLayers layers j) := by
  intro layer hm
  obtain ⟨block, hb, hl⟩ := List.mem_flatten.mp hm
  have heq : block = layers := List.eq_of_mem_replicate hb
  exact h layer (heq ▸ hl)

theorem quarterWavePair_loss (k n₁ n₂ : ℝ) :
    integratedLoss (quarterWavePair k n₁ n₂) = 0 := by
  simp [quarterWavePair, quarterWaveLayer, integratedLoss]

theorem quarterWavePair_thickness (k n₁ n₂ : ℝ) :
    totalThickness (quarterWavePair k n₁ n₂) =
      Real.pi / (2 * k) * (1 / n₁ + 1 / n₂) := by
  simp only [quarterWavePair, totalThickness, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, quarterWaveLayer]
  field_simp

theorem quarterWavePair_thickness_lt {k n₁ n₂ : ℝ} (hk : 0 < k)
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) :
    totalThickness (quarterWavePair k n₁ n₂) < Real.pi / k := by
  have h₁ : 1 / n₁ < (1 : ℝ) := (div_lt_one (by linarith)).mpr hn₁
  have h₂ : 1 / n₂ < (1 : ℝ) := (div_lt_one (by linarith)).mpr hn₂
  rw [quarterWavePair_thickness]
  have hc : 0 < Real.pi / (2 * k) := by positivity
  calc
    _ < Real.pi / (2 * k) * 2 := mul_lt_mul_of_pos_left (by linarith) hc
    _ = _ := by ring

#print axioms refractiveIndex_quarterWave
#print axioms layerTransfer_quarterWave
#print axioms quarterWaveLayer_admissible
#print axioms quarterWavePair_transfer
#print axioms stackTransfer_append
#print axioms totalThickness_append
#print axioms integratedLoss_append
#print axioms repeatPhysicalLayers_transfer
#print axioms repeatPhysicalLayers_thickness
#print axioms repeatPhysicalLayers_loss
#print axioms repeatPhysicalLayers_admissible
#print axioms quarterWavePair_loss
#print axioms quarterWavePair_thickness
#print axioms quarterWavePair_thickness_lt
end OQ7
