import work.PhysicalPerturbationZero
import work.CompactParameterNeighborhood

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set Filter
open scoped Topology Ring

theorem physicalPerturbed_preserves_compact_bracket (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (a b target m cap : ℝ) (hcap : 0 < cap)
    (hX : ∀ θ ∈ Icc a b, 0 < physicalPerturbedExtinction k B .plus 0 θ α β)
    (hG : ∀ θ ∈ Icc a b, m < physicalPerturbedAsymmetry k B 0 θ α β)
    (hlo : physicalPerturbedExtinction k B .plus 0 a α β < target)
    (hhi : target < physicalPerturbedExtinction k B .plus 0 b α β) :
    ∃ ν : ℝ, 0 < ν ∧ ν < cap ∧
      physicalPerturbedExtinction k B .plus ν a α β < target ∧
      target < physicalPerturbedExtinction k B .plus ν b α β ∧
      ∀ θ ∈ Icc a b, IsUnit (physicalElectricOperator k B ν θ α β) ∧
        0 < physicalPerturbedExtinction k B .plus ν θ α β ∧
        m < physicalPerturbedAsymmetry k B ν θ α β := by
  let L := fun x : ℝ × ℝ => physicalElectricOperator k B x.1 x.2 α β
  let X := fun x : ℝ × ℝ => physicalPerturbedExtinction k B .plus x.1 x.2 α β
  let G := fun x : ℝ × ℝ => physicalPerturbedAsymmetry k B x.1 x.2 α β
  let U : Set (ℝ × ℝ) := {x | IsUnit (L x)}
  have hU : IsOpen U := (Units.isOpen (R := BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B)).preimage
    (physicalElectricOperator_joint_continuous k B α β)
  let V : Set (ℝ × ℝ) := {x | x ∈ U ∧ 0 < X x}
  have hV : IsOpen V := isOpen_strict_region_of_continuousAt_on_open U hU X
    (fun x hx => physicalPerturbedExtinction_joint_continuousAt k B .plus α β x hx) 0
  let W : Set (ℝ × ℝ) := {x | x ∈ V ∧ m < G x}
  have hW : IsOpen W := isOpen_strict_region_of_continuousAt_on_open V hV G
    (fun x hx => physicalPerturbedAsymmetry_joint_continuousAt k B α β x hx.1 (ne_of_gt hx.2)) m
  obtain ⟨r, hr, htube⟩ := exists_uniform_parameter_neighborhood_of_compact (Icc a b) isCompact_Icc W hW
    (fun θ hθ => ⟨⟨physicalElectricOperator_zero_isUnit k hk B θ α β hα hβ, hX θ hθ⟩, hG θ hθ⟩)
  have hca : ContinuousAt (fun ν : ℝ => physicalPerturbedExtinction k B .plus ν a α β) 0 :=
    (physicalPerturbedExtinction_joint_continuousAt k B .plus α β (0, a)
      (physicalElectricOperator_zero_isUnit k hk B a α β hα hβ)).comp
        (f := fun ν : ℝ => (ν, a)) (continuousAt_id.prodMk continuousAt_const)
  have hcb : ContinuousAt (fun ν : ℝ => physicalPerturbedExtinction k B .plus ν b α β) 0 :=
    (physicalPerturbedExtinction_joint_continuousAt k B .plus α β (0, b)
      (physicalElectricOperator_zero_isUnit k hk B b α β hα hβ)).comp
        (f := fun ν : ℝ => (ν, b)) (continuousAt_id.prodMk continuousAt_const)
  obtain ⟨e, he, hend⟩ := Metric.eventually_nhds_iff.mp
    ((hca.eventually_lt_const hlo).and (hcb.eventually_const_lt hhi))
  let ν := min (r / 2) (min (e / 2) (cap / 2))
  have hν : 0 < ν := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hνr : ν < r := by have h := min_le_left (r / 2) (min (e / 2) (cap / 2)); linarith
  have hνe : ν < e := by
    have h := (min_le_right (r / 2) (min (e / 2) (cap / 2))).trans (min_le_left (e / 2) (cap / 2))
    linarith
  have hνcap : ν < cap := by
    have h := (min_le_right (r / 2) (min (e / 2) (cap / 2))).trans (min_le_right (e / 2) (cap / 2))
    linarith
  have hp := hend (show dist ν 0 < e by simpa [dist_zero_right, Real.norm_eq_abs, abs_of_pos hν] using hνe)
  refine ⟨ν, hν, hνcap, hp.1, hp.2, ?_⟩
  intro θ hθ
  have ht := htube ν (by simpa only [abs_of_pos hν] using hνr) θ hθ
  exact ⟨ht.1.1, ht.1.2, ht.2⟩

end OQ7Prescribed
