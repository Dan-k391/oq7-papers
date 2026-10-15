import GeneralizedResearch.ActualStackContinuity
import GeneralizedResearch.MaxwellIntegrals
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Literal regional Maxwell equations of the very same actual stack states
whose interface matching and transverse L² properties have been proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.ActualStackMaxwell
open ActualStackBeamFields ActualStackContinuity ObliqueVacuum ObliqueMaxwell ObliqueFamily
open FourierMaxwell MaxwellIntegrals
open MeasureTheory Set
open scoped Matrix
abbrev Transverse := BeamAveraging.Transverse

def Satisfies (k : ℝ) (R Q : RMat) (F : ℝ → ℝ → ℝ → Vec3 × Vec3) : Prop :=
  ∀ x y z,
    curl (fun x y z => (F x y z).1) x y z = (Complex.I * (k : ℂ)) • (F x y z).2 ∧
    curl (fun x y z => (F x y z).2) x y z =
      (-(Complex.I * (k : ℂ))) • constitutive R Q (F x y z).1

theorem curl_zshift (F : ℝ → ℝ → ℝ → Vec3) (d x y z : ℝ) :
    curl (fun x y z => F x y (z - d)) x y z = curl F x y (z - d) := by
  ext i; fin_cases i <;> simp [curl]
  · exact deriv_comp_sub_const (fun r => F x y r 1) d z
  · exact deriv_comp_sub_const (fun r => F x y r 0) d z

def localPair (r k : ℝ) (R Q : RMat) (u : Transverse → Channel → ℂ)
    (d x y z : ℝ) : Vec3 × Vec3 :=
  trace r k (fun q => transfer k (WithLp.ofLp q) R Q (z - d) *ᵥ u q) x y

theorem localPair_eq (r k : ℝ) (R Q : RMat) (u : Transverse → Channel → ℂ)
    (d x y z : ℝ) : localPair r k R Q u d x y z =
      (superposedElectric r k R Q u (x, y, z - d),
       superposedMagnetic r k R Q u (x, y, z - d)) := by
  rfl

theorem local_maxwell (r k : ℝ) (hk : k ≠ 0) (R Q : RMat)
    (u : Transverse → Channel → ℂ) (hu : ContinuousOn u (BeamPackets.disk r)) (d : ℝ) :
    Satisfies k R Q (localPair r k R Q u d) := by
  intro x y z
  simp only [localPair_eq]
  rw [curl_zshift (fun x y z => superposedElectric r k R Q u (x, y, z)),
    curl_zshift (fun x y z => superposedMagnetic r k R Q u (x, y, z))]
  exact superposed_maxwell r k hk R Q u hu x y (z - d)

def absorber (p : Parameters) (r : ℝ) (u : Transverse → Channel → ℂ)
    (x y z : ℝ) : Vec3 × Vec3 :=
  trace r p.k (fun q => p.absorberState (WithLp.ofLp q) (u q) z) x y
def plate (p : Parameters) (r : ℝ) (u : Transverse → Channel → ℂ)
    (x y z : ℝ) : Vec3 × Vec3 :=
  trace r p.k (fun q => p.plateState (WithLp.ofLp q) (u q) z) x y
def vacuumLeft (p : Parameters) (r : ℝ) (u : Transverse → Channel → ℂ)
    (x y z : ℝ) : Vec3 × Vec3 :=
  trace r p.k (fun q => p.leftVacuumState (WithLp.ofLp q) (u q) z) x y
def vacuumRight (p : Parameters) (r : ℝ) (u : Transverse → Channel → ℂ)
    (x y z : ℝ) : Vec3 × Vec3 :=
  trace r p.k (fun q => p.rightVacuumState (WithLp.ofLp q) (u q) z) x y

/-- Both material regions and both exteriors satisfy the literal classical
Maxwell equations. These are the exact scattering-derived states, not assumed
solutions or independently chosen regional fields. -/
theorem actual_regional_maxwell (p : Parameters) (r : ℝ) (hr : r < p.k)
    (u : Transverse → Channel → ℂ) (hu : ContinuousOn u (BeamPackets.disk r)) :
    Satisfies p.k 1 (absorberLoss p.η) (absorber p r u) ∧
      Satisfies p.k (PlanarPlateBridge.tensor p.j p.t) 0 (plate p r u) ∧
      Satisfies p.k 1 0 (vacuumLeft p r u) ∧
      Satisfies p.k 1 0 (vacuumRight p r u) := by
  have hi := initial_continuousOn p r hr u hu
  have ha := (states_continuousOn p r hr u hu p.h).1
  constructor
  · simpa only [Satisfies, absorber, Parameters.absorberState, localPair, sub_zero] using
      local_maxwell r p.k p.hk.ne' 1 (absorberLoss p.η) _ hi.1 0
  constructor
  · exact local_maxwell r p.k p.hk.ne' (PlanarPlateBridge.tensor p.j p.t) 0 _ ha p.h
  constructor
  · simpa only [Satisfies, vacuumLeft, Parameters.leftVacuumState, localPair, sub_zero] using
      local_maxwell r p.k p.hk.ne' 1 0 _ hi.1 0
  · exact local_maxwell r p.k p.hk.ne' 1 0 _ hi.2 (p.h + p.thickness)

theorem actual_interfaces (p : Parameters) (r : ℝ) (hr : r < p.k)
    (u : Transverse → Channel → ℂ) (x y : ℝ) :
    vacuumLeft p r u x y 0 = absorber p r u x y 0 ∧
      absorber p r u x y p.h = plate p r u x y p.h ∧
      plate p r u x y (p.h + p.thickness) = vacuumRight p r u x y (p.h + p.thickness) :=
  integrated_interfaces p r hr u x y

theorem curl_const_smul (F : ℝ → ℝ → ℝ → Vec3) (c : ℂ) (x y z : ℝ) :
    curl (fun x y z => c • F x y z) x y z = c • curl F x y z := by
  ext i; fin_cases i <;> simp [curl, deriv_const_mul_field, mul_sub]

def physical (F : ℝ → ℝ → ℝ → Vec3 × Vec3) (x y z : ℝ) : Vec3 × Vec3 :=
  ((Real.sqrt 2 : ℂ) • (F x y z).1, (Real.sqrt 2 : ℂ) • (F x y z).2)

theorem physical_maxwell {k : ℝ} {R Q : RMat} {F : ℝ → ℝ → ℝ → Vec3 × Vec3}
    (h : Satisfies k R Q F) : Satisfies k R Q (physical F) := by
  intro x y z
  have hm := h x y z
  simp only [physical, curl_const_smul, hm.1, hm.2, constitutive_smul, smul_smul]
  constructor <;> congr 1 <;> ring

end GeneralizedResearch.ActualStackMaxwell
