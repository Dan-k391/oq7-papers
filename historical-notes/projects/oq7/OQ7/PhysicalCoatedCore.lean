import OQ7.CoreExponential
import OQ7.MatchingSheet

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7.CoreConstruction
open Filter
open scoped Topology Matrix

/-- The complete finite physical core and the two fixed-count dielectric coatings. -/
def physicalCoatedCore (k P Q M : ℝ) (m jL jR : ℕ) (ℓ : ℝ × ℝ) : List HomogeneousLayer :=
  coatingLayers k P ℓ.1 jL ++ physicalUnmatchedCore k P Q M m ++
    coatingLayers k P ℓ.2 jR

theorem physicalCoatedCore_transfer {k P : ℝ} (hk : 0 < k) (hP : 0 < P)
    (Q M : ℝ) (m : ℕ) {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR) (ℓ : ℝ × ℝ) :
    stackTransfer k (physicalCoatedCore k P Q M m jL jR ℓ) =
      (-1 : ℂ) ^ (jL + jR + (m + 1)) •
        logCoatedTransfer (strippedCellTransfer k P Q M m ^ m) ℓ := by
  rw [physicalCoatedCore, physicallyCoated_transfer hk P ℓ.1 ℓ.2 hjL hjR,
    physicalUnmatchedCore_transferFactorization hk hP]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← pow_add,
    logCoatedTransfer_eq_physical_scale]

theorem physicalCoatedCore_loss {Q : ℝ} {m : ℕ} (hQ : Q ≠ 0) (hm : m ≠ 0)
    (k P M : ℝ) (jL jR : ℕ) (ℓ : ℝ × ℝ) :
    integratedLoss (physicalCoatedCore k P Q M m jL jR ℓ) = M := by
  rw [physicalCoatedCore, physicallyCoated_loss, physicalUnmatchedCore_loss hQ hm]

theorem physicalCoatedCore_admissible {k P Q M : ℝ} {m jL jR : ℕ} {ℓ : ℝ × ℝ}
    (hL : StackAdmissible P Q (coatingLayers k P ℓ.1 jL))
    (hcore : StackAdmissible P Q (physicalUnmatchedCore k P Q M m))
    (hR : StackAdmissible P Q (coatingLayers k P ℓ.2 jR)) :
    StackAdmissible P Q (physicalCoatedCore k P Q M m jL jR ℓ) := by
  intro layer hm
  simp only [physicalCoatedCore, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact hL layer hm
  · exact hcore layer hm
  · exact hR layer hm

theorem physicalCoatedCore_thickness_lt {k P Q M : ℝ} {m jL jR : ℕ} {ℓ : ℝ × ℝ}
    (hL : totalThickness (coatingLayers k P ℓ.1 jL) < (jL : ℝ) * Real.pi / k)
    (hR : totalThickness (coatingLayers k P ℓ.2 jR) < (jR : ℝ) * Real.pi / k) :
    totalThickness (physicalCoatedCore k P Q M m jL jR ℓ) <
      (m : ℝ) * coreCellLength k P +
        (coreCellLength k P + ((jL + jR : ℕ) : ℝ) * Real.pi / k) := by
  simp only [physicalCoatedCore, totalThickness_append, physicalUnmatchedCore_thickness,
    Nat.cast_add, add_mul, add_div, one_mul]
  linarith

/-- Convergent exact-matching logs stay within the strict material bounds of fixed coatings. -/
theorem physicalCoatedCore_eventually_physical {k P Q M : ℝ}
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hM : 0 < M)
    {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR) {ℓ₀ : ℝ × ℝ}
    (hℓL : |ℓ₀.1| / (jL : ℝ) < Real.log P / 2)
    (hℓR : |ℓ₀.2| / (jR : ℝ) < Real.log P / 2)
    {ℓ : ℕ → ℝ × ℝ} (hℓ : Tendsto ℓ atTop (𝓝 ℓ₀)) :
    ∀ᶠ m : ℕ in atTop,
      StackAdmissible P Q (physicalCoatedCore k P Q M m jL jR (ℓ m)) ∧
      integratedLoss (physicalCoatedCore k P Q M m jL jR (ℓ m)) = M ∧
      totalThickness (physicalCoatedCore k P Q M m jL jR (ℓ m)) <
        (m : ℝ) * coreCellLength k P +
          (coreCellLength k P + ((jL + jR : ℕ) : ℝ) * Real.pi / k) := by
  have hL := ((continuous_fst.tendsto ℓ₀).comp hℓ).eventually
    (coatingLayers_eventually_physical hk hP hQ.le hjL hℓL)
  have hR := ((continuous_snd.tendsto ℓ₀).comp hℓ).eventually
    (coatingLayers_eventually_physical hk hP hQ.le hjR hℓR)
  filter_upwards [hL, hR, physicalUnmatchedCore_eventually_admissible hk hP hQ hM,
    eventually_gt_atTop (0 : ℕ)] with m hmL hmR hmcore hm
  exact ⟨physicalCoatedCore_admissible hmL.1 hmcore.1 hmR.1,
    physicalCoatedCore_loss hQ.ne' hm.ne' k P M jL jR (ℓ m),
    physicalCoatedCore_thickness_lt hmL.2 hmR.2⟩

theorem exists_eventually_physicalCoatedCore {k P Q M : ℝ}
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hM : 0 < M)
    {ℓ₀ : ℝ × ℝ} {ℓ : ℕ → ℝ × ℝ} (hℓ : Tendsto ℓ atTop (𝓝 ℓ₀)) :
    ∃ jL jR : ℕ, 0 < jL ∧ 0 < jR ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ m : ℕ in atTop,
        StackAdmissible P Q (physicalCoatedCore k P Q M m jL jR (ℓ m)) ∧
        integratedLoss (physicalCoatedCore k P Q M m jL jR (ℓ m)) = M ∧
        totalThickness (physicalCoatedCore k P Q M m jL jR (ℓ m)) <
          (m : ℝ) * coreCellLength k P + C := by
  obtain ⟨jL, hjL, hℓL⟩ := exists_coatingPairCount hP ℓ₀.1
  obtain ⟨jR, hjR, hℓR⟩ := exists_coatingPairCount hP ℓ₀.2
  refine ⟨jL, jR, hjL, hjR, coreCellLength k P + ((jL + jR : ℕ) : ℝ) * Real.pi / k, ?_,
    physicalCoatedCore_eventually_physical hk hP hQ hM hjL hjR hℓL hℓR hℓ⟩
  have hc := coreCellLength_pos hk (by linarith : 0 < P)
  positivity

theorem coreCellLength_scaled {k : ℝ} (hk : k ≠ 0) (P : ℝ) :
    k * coreCellLength k P = Real.pi / Real.sqrt P := by
  unfold coreCellLength
  rw [← div_div, ← mul_div_assoc, mul_div_cancel₀ _ hk]

theorem physicalCoatedCore_eventually_dimensionless_thickness {k P Q M : ℝ}
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hM : 0 < M)
    {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR) {ℓ₀ : ℝ × ℝ}
    (hℓL : |ℓ₀.1| / (jL : ℝ) < Real.log P / 2)
    (hℓR : |ℓ₀.2| / (jR : ℝ) < Real.log P / 2)
    {ℓ : ℕ → ℝ × ℝ} (hℓ : Tendsto ℓ atTop (𝓝 ℓ₀)) :
    ∀ᶠ m : ℕ in atTop,
      k * totalThickness (physicalCoatedCore k P Q M m jL jR (ℓ m)) <
        (m : ℝ) * Real.pi / Real.sqrt P +
          (Real.pi / Real.sqrt P + ((jL + jR : ℕ) : ℝ) * Real.pi) := by
  filter_upwards [physicalCoatedCore_eventually_physical hk hP hQ hM hjL hjR hℓL hℓR hℓ]
    with m hm
  apply (mul_lt_mul_of_pos_left hm.2.2 hk).trans_eq
  have hd := coreCellLength_scaled hk.ne' P
  have hc : k * (((jL + jR : ℕ) : ℝ) * Real.pi / k) =
      ((jL + jR : ℕ) : ℝ) * Real.pi := mul_div_cancel₀ _ hk.ne'
  calc
    k * ((m : ℝ) * coreCellLength k P +
      (coreCellLength k P + ((jL + jR : ℕ) : ℝ) * Real.pi / k)) =
        (m : ℝ) * (k * coreCellLength k P) +
          (k * coreCellLength k P + k * (((jL + jR : ℕ) : ℝ) * Real.pi / k)) := by ring
    _ = _ := by rw [hd, hc]; ring

#print axioms physicalCoatedCore_transfer
#print axioms physicalCoatedCore_loss
#print axioms physicalCoatedCore_admissible
#print axioms physicalCoatedCore_thickness_lt
#print axioms physicalCoatedCore_eventually_physical
#print axioms exists_eventually_physicalCoatedCore
#print axioms coreCellLength_scaled
#print axioms physicalCoatedCore_eventually_dimensionless_thickness
end OQ7.CoreConstruction
