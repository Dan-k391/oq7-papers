import OQ7.Layers
import OQ7.Transfer
import OQ7.Envelope

namespace OQ7

noncomputable section

/-- Fixed physical and exact power targets from Theorem 5.1. -/
structure PhysicalParameters where
  k : ℝ
  P : ℝ
  Q : ℝ
  M : ℝ
  T : ℝ
  a : ℝ
  k_pos : 0 < k
  P_gt_one : 1 < P
  Q_pos : 0 < Q
  M_pos : 0 < M
  active : ScalarEnvelope.ActiveTarget T a

/-- The response is computed from the finite product of actual homogeneous layers. -/
def stackReflectionLeft (k : ℝ) (layers : List HomogeneousLayer) : ℂ :=
  transferReflectionLeft (waveTransfer (stackTransfer k layers))

def stackReflectionRight (k : ℝ) (layers : List HomogeneousLayer) : ℂ :=
  transferReflectionRight (waveTransfer (stackTransfer k layers))

def stackTransmission (k : ℝ) (layers : List HomogeneousLayer) : ℂ :=
  transferTransmissionRight (waveTransfer (stackTransfer k layers))

def stackTransmissionPower (k : ℝ) (layers : List HomogeneousLayer) : ℝ :=
  transmissionPower (stackTransmission k layers)

def stackMeanAbsorptance (k : ℝ) (layers : List HomogeneousLayer) : ℝ :=
  meanAbsorptance (stackReflectionLeft k layers) (stackReflectionRight k layers)
    (stackTransmission k layers)

def stackAsymmetry (k : ℝ) (layers : List HomogeneousLayer) : ℝ :=
  |absorptanceLeft (stackReflectionLeft k layers) (stackTransmission k layers) -
    absorptanceRight (stackReflectionRight k layers) (stackTransmission k layers)|

/-- Exact equalities, all layers counted, no fixed layer count or minimum layer width. -/
def exactTargetClass (p : PhysicalParameters) (L : ℝ) : Set (List HomogeneousLayer) :=
  { layers | StackAdmissible p.P p.Q layers ∧
      integratedLoss layers = p.M ∧ totalThickness layers ≤ L ∧
      stackTransmissionPower p.k layers = p.T ∧
      stackMeanAbsorptance p.k layers = p.a }

/-- Its intended use is at budgets for which `exactTargetClass` is nonempty. -/
def optimalAsymmetry (p : PhysicalParameters) (L : ℝ) : ℝ :=
  sSup (stackAsymmetry p.k '' exactTargetClass p L)

def asymptoticCoefficient (p : PhysicalParameters) : ℝ :=
  ScalarEnvelope.alpha p.T p.a * Real.pi ^ 2 * (p.k * p.M) ^ 4 /
    (3 * p.P * p.Q ^ 2)

/-- The exact original physical target. Its proof is `OQ7.theorem51` in
`SharpPhysicalConstruction`, built from the Maxwell Gram identity, uniform lower
floor, actual exactly matched dielectric layers, and the all-budget supremum squeeze. -/
def Theorem51Statement (p : PhysicalParameters) : Prop :=
  (∀ᶠ L : ℝ in Filter.atTop, (exactTargetClass p L).Nonempty) ∧
  (∀ (L : ℝ) (layers : List HomogeneousLayer), layers ∈ exactTargetClass p L →
    stackAsymmetry p.k layers < ScalarEnvelope.D0 p.T p.a) ∧
  Filter.Tendsto
    (fun L : ℝ => (p.k * L) ^ 2 *
      (ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L))
    Filter.atTop (nhds (asymptoticCoefficient p))

end
end OQ7
