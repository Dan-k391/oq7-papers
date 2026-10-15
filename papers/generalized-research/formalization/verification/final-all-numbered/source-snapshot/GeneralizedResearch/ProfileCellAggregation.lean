import GeneralizedResearch.ProfileResource

/-! Arbitrary finite disjoint selected cells, with the complementary deposited
Gram explicitly constructed from the actual field integrals. -/
noncomputable section
namespace GeneralizedResearch.HelmholtzProfile.Profile
open Set MeasureTheory OQ7
open scoped Matrix ComplexOrder
variable {k : ℝ} (F : Profile k)

theorem disjoint_cell_rest {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {D : ℝ}
    (hD : 0 ≤ D)
    (hsub : ∀ j ∈ s, Ioc (a j) (b j) ⊆ Ioc 0 D)
    (hdis : Set.Pairwise (s : Set ι) (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    fluxDefect (F.field D) - ∑ j ∈ s, F.deposited (a j) (b j) =
      (2 * (k : ℂ)) • weightedGram
        (volume.restrict (Ioc 0 D \ ⋃ j ∈ s, Ioc (a j) (b j)))
        F.q (fun x j => F.field x 0 j) := by
  classical
  let U : Set ℝ := ⋃ j ∈ s, Ioc (a j) (b j)
  have hU : MeasurableSet U := s.measurableSet_biUnion (fun _ _ => measurableSet_Ioc)
  have hUs : U ⊆ Ioc 0 D := by
    intro x hx
    obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
    exact hsub j hj hx
  rw [← F.deposited_total hD]
  ext i j
  have hint := (F.weighted_entry_integrable i j 0 D).1
  have hc (r : ι) (hr : r ∈ s) :
      IntegrableOn (fun x => (F.q x : ℂ) * star (F.field x 0 i) * F.field x 0 j)
        (Ioc (a r) (b r)) := hint.mono_set (hsub r hr)
  have hu := integral_biUnion_finset s (fun _ _ => measurableSet_Ioc) hdis hc
  have hd := integral_inter_add_sdiff hU hint
  rw [Set.inter_eq_right.mpr hUs] at hd
  change (∫ x in U, (F.q x : ℂ) * star (F.field x 0 i) * F.field x 0 j) +
    (∫ x in Ioc 0 D \ U, (F.q x : ℂ) * star (F.field x 0 i) * F.field x 0 j) = _ at hd
  rw [hu] at hd
  simp only [deposited, weightedGram, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  change (2 * (k : ℂ)) * (∫ x in Ioc 0 D, (F.q x : ℂ) * star (F.field x 0 i) * F.field x 0 j) -
    (2 * (k : ℂ)) * (∑ r ∈ s, ∫ x in Ioc (a r) (b r), (F.q x : ℂ) * star (F.field x 0 i) * F.field x 0 j) =
    (2 * (k : ℂ)) * (∫ x in Ioc 0 D \ U, (F.q x : ℂ) * star (F.field x 0 i) * F.field x 0 j)
  rw [← hd]
  ring

theorem disjoint_cell_rest_posSemidef {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {D : ℝ}
    (hk : 0 ≤ k) (hD : 0 ≤ D)
    (hsub : ∀ j ∈ s, Ioc (a j) (b j) ⊆ Ioc 0 D)
    (hdis : Set.Pairwise (s : Set ι) (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (fluxDefect (F.field D) - ∑ j ∈ s, F.deposited (a j) (b j)).PosSemidef := by
  rw [F.disjoint_cell_rest s a b hD hsub hdis]
  apply Matrix.PosSemidef.smul
  · apply weightedGram_posSemidef
    · intro i j
      exact (F.weighted_entry_integrable i j 0 D).1.mono_set sdiff_subset
    · exact ae_of_all _ F.passive
  · exact RCLike.nonneg_iff.mpr ⟨by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk, by simp⟩

/-- The literal arbitrary-disjoint-cell aggregation, with no equal-width
partition or omitted-complement hypothesis. -/
theorem disjoint_sqrt_aggregate {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {D : ℝ}
    (hk : 0 ≤ k) (hD : 0 ≤ D)
    (hsub : ∀ j ∈ s, Ioc (a j) (b j) ⊆ Ioc 0 D)
    (hdis : Set.Pairwise (s : Set ι) (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ j ∈ s, Real.sqrt ((F.deposited (a j) (b j)).det.re)) ≤ Real.sqrt (F.invariant D) := by
  exact posSemidef_sqrt_det_aggregate s (fun j => F.deposited (a j) (b j)) (fluxDefect (F.field D))
    (fun j _ => F.deposited_posSemidef hk _ _)
    (F.disjoint_cell_rest_posSemidef s a b hk hD hsub hdis)

theorem disjoint_resource_cells {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {D P Q : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hD : 0 ≤ D)
    (hsub : ∀ j ∈ s, Ioc (a j) (b j) ⊆ Ioc 0 D)
    (hdis : Set.Pairwise (s : Set ι) (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (hab : ∀ j ∈ s, a j ≤ b j)
    (hwidth : ∀ j ∈ s, b j - a j ≤ Real.pi / (k * Real.sqrt P))
    (hp : ∀ j ∈ s, ∀ z ∈ Ioo (a j) (b j), F.p z ≤ P)
    (hq : ∀ j ∈ s, ∀ z ∈ Ioo (a j) (b j), 0 ≤ F.q z ∧ F.q z ≤ Q) :
    Q / P * (∑ j ∈ s, ResourceScalar.g (k * Real.sqrt P * (∫ z in a j..b j, F.q z) / Q)) ≤
      Real.sqrt (F.invariant D) := by
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun j hj => F.cell_sqrt_det_lower hk hP hQ (hp j hj) (hq j hj)
    (hab j hj) (hwidth j hj))).trans
  exact F.disjoint_sqrt_aggregate s a b hk.le hD hsub hdis

end GeneralizedResearch.HelmholtzProfile.Profile
