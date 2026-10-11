import OQ7.PhysicalIntegrals
import OQ7.PhysicalClass
import OQ7.Target

noncomputable section

namespace OQ7

open Set MeasureTheory

/-- The physical class in Section 4: finite passive dielectric stacks with caps and
exact loss mass on a selected interval. Other finite passive layers are allowed
outside that interval; their material caps need not equal `P` and `Q`. -/
def SelectedResourceClass (P Q M L : ℝ) (layers : List HomogeneousLayer) : Prop :=
  FinitePhysicalStack layers ∧ ∃ a : ℝ,
    0 ≤ a ∧
    (∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P) ∧
    (∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧
      stackLossProfile layers z ≤ Q) ∧
    (∫ z in a..a + L, stackLossProfile layers z) = M

/-- A global thickness budget selects the whole stack, padded by zero-loss vacuum. -/
theorem selectedResourceClass_of_admissible {P Q M L : ℝ}
    (hP : 1 ≤ P) (hQ : 0 ≤ Q) {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (hM : integratedLoss layers = M)
    (hL : totalThickness layers ≤ L) : SelectedResourceClass P Q M L layers := by
  refine ⟨finitePhysicalStack_of_admissible h, 0, le_rfl, ?_, ?_, ?_⟩
  · intro z _
    exact (stackRealProfile_bounds hP h z).2
  · intro z _
    exact stackLossProfile_bounds hQ h z
  · simpa only [zero_add, stackLossProfile_integral_budget hQ h hL] using hM

/-- Exact-target classes from Section 5 are included in the original Section 4 class. -/
theorem selectedResourceClass_of_exactTarget {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (h : layers ∈ exactTargetClass p L) :
    SelectedResourceClass p.P p.Q p.M L layers :=
  selectedResourceClass_of_admissible p.P_gt_one.le p.Q_pos.le h.1 h.2.1 h.2.2.1

#print axioms selectedResourceClass_of_admissible
#print axioms selectedResourceClass_of_exactTarget

end OQ7
