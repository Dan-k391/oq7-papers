import PrescribedExtinction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual three-dimensional weak Maxwell equations, radiation condition, and
plane-wave cross sections. All equations below are definitions of the physical
problem, not assumed conclusions about its solutions. No volume operator or
optical theorem is smuggled into a structure field. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Interval

inductive Direction | plus | minus
  deriving DecidableEq

def Direction.sign : Direction → ℝ
  | .plus => 1
  | .minus => -1

def cross (u v : Vector) : Vector := WithLp.toLp 2
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def realDot (x y : Position) : ℝ := ∑ i, x i * y i

def planePhase (k : ℝ) (σ : Direction) (x : Position) : ℂ :=
  Complex.exp (Complex.I * ((σ.sign * k * x 2 : ℝ) : ℂ))

def incidentElectric (k : ℝ) (σ : Direction) : Field :=
  fun x => planePhase k σ x • basisC 1

/-- Magnetic field in impedance-normalized coordinates Z₀ H. -/
def incidentMagnetic (k : ℝ) (σ : Direction) : Field :=
  fun x => (σ.sign : ℂ) • cross (basisC 2) (incidentElectric k σ x)

/-- Classical curl, used on smooth compactly supported test functions only. -/
def curl (F : Field) (x : Position) : Vector := WithLp.toLp 2
  ![(fderiv ℝ F x (basisR 1)) 2 - (fderiv ℝ F x (basisR 2)) 1,
    (fderiv ℝ F x (basisR 2)) 0 - (fderiv ℝ F x (basisR 0)) 2,
    (fderiv ℝ F x (basisR 0)) 1 - (fderiv ℝ F x (basisR 1)) 0]

/-- Distributional curl via its action on all smooth compactly supported vector tests.
The pairing is bilinear, so curl is formally self-transpose without conjugation. -/
def HasWeakCurl (F G : Field) : Prop :=
  ∀ φ : Field, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x : Position, bilinear (F x) (curl φ x)) =
      ∫ x : Position, bilinear (G x) (φ x)

def LocallySquareIntegrable (F : Field) : Prop :=
  ∀ K : Set Position, IsCompact K → MemLp F 2 (volume.restrict K)

/-- μ=I is built into the two Maxwell curl equations. -/
def WeakMaxwell (k : ℝ) (B : TwoLayerBody) (E H : Field) : Prop :=
  LocallySquareIntegrable E ∧ LocallySquareIntegrable H ∧
  HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x) ∧
  HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) •
    tensorApply (B.permittivity x) (E x))

/-- Uniform Silver-Müller radiation condition for the scattered fields.
The quantifier covers the entire sphere, not just two specular channels. -/
def Outgoing (Es Hs : Field) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
    ∀ x : Position, ρ ≤ ‖x‖ →
      ‖x‖ * ‖cross (Hs x) (complexify (‖x‖⁻¹ • x)) - Es x‖ < ε

def polarization (B : TwoLayerBody) (E : Field) : Field :=
  fun x => tensorApply (B.susceptibility x) (E x)

/-- A scattering state is a pair of actual fields, not a free choice of power data. -/
structure ScatteringState (k : ℝ) (B : TwoLayerBody) (σ : Direction) where
  electric : Field
  magnetic : Field
  maxwell : WeakMaxwell k B electric magnetic
  outgoing : Outgoing (fun x => electric x - incidentElectric k σ x)
    (fun x => magnetic x - incidentMagnetic k σ x)
  current_memLp : MemLp (polarization B electric) 2 volume

def transverseProjection (n : Position) (v : Vector) : Vector :=
  v - (∑ i, (n i : ℂ) * v i) • complexify n

/-- The full vector far-field expression (6), with physical area normalization. -/
def currentFarField (k : ℝ) (B : TwoLayerBody) (E : Field) (n : Position) : Vector :=
  ((k ^ 2 / (4 * Real.pi) : ℝ) : ℂ) • transverseProjection n
    (∫ x in B.domain, Complex.exp (-Complex.I * ((k * realDot n x : ℝ) : ℂ)) •
      polarization B E x)

def sphereDirection (θ φ : ℝ) : Position := WithLp.toLp 2
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- Optical work cross section for a unit-electric-amplitude incident plane wave. -/
def extinction (k : ℝ) (B : TwoLayerBody) (σ : Direction) (E : Field) : ℝ :=
  k * (∫ x in B.domain, pairing (incidentElectric k σ x) (polarization B E x)).im

/-- True local dielectric power dissipation, divided by common incident intensity. -/
def absorption (k : ℝ) (B : TwoLayerBody) (E : Field) : ℝ :=
  k * ∫ x in B.domain, (quadratic (B.permittivity x) (E x)).im

/-- Total radiation integral in spherical coordinates, including both polarizations.
Identifying this current expression with the outgoing field flux is still unproved. -/
def scattering (k : ℝ) (B : TwoLayerBody) (E : Field) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
    squareNorm (currentFarField k B E (sphereDirection θ φ)) * Real.sin θ

def normalizedAsymmetry (k : ℝ) (B : TwoLayerBody) (Ep Em : Field) : ℝ :=
  |absorption k B Ep - absorption k B Em| / extinction k B .plus Ep

/-- The exact requested statement, as an UNPROVED proposition.
No proof declaration for this proposition is present in this partial project. -/
def Theorem11Statement : Prop :=
  ∀ k P Q target : ℝ, 0 < k → 1 < P → 0 < Q → 0 < target →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ B : TwoLayerBody, B.admissible P Q ∧
        ∃ sp : ScatteringState k B .plus,
          ∃ sm : ScatteringState k B .minus,
            extinction k B .plus sp.electric = target ∧
            extinction k B .minus sm.electric = target ∧
            1 - ε < normalizedAsymmetry k B sp.electric sm.electric ∧
            normalizedAsymmetry k B sp.electric sm.electric < 1

theorem planePhase_norm (k : ℝ) (σ : Direction) (x : Position) :
    ‖planePhase k σ x‖ = 1 := by
  simp [planePhase, Complex.norm_exp]

theorem incidentElectric_squareNorm (k : ℝ) (σ : Direction) (x : Position) :
    squareNorm (incidentElectric k σ x) = 1 := by
  simp [squareNorm, incidentElectric, basisC, Fin.sum_univ_succ,
    Complex.normSq_eq_norm_sq, planePhase_norm]

theorem incidentElectric_minus_conjugate (k : ℝ) (x : Position) :
    incidentElectric k .minus x = WithLp.toLp 2
      (fun i => star (incidentElectric k .plus x i)) := by
  ext i
  by_cases hi : i = 1
  · subst i
    simp [incidentElectric, planePhase, Direction.sign, basisC,
      ← Complex.exp_conj, mul_comm]
  · simp [incidentElectric, basisC, hi]

theorem sphereDirection_unit (θ φ : ℝ) : ‖sphereDirection θ φ‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [sphereDirection, Fin.sum_univ_succ]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

end OQ7Prescribed
