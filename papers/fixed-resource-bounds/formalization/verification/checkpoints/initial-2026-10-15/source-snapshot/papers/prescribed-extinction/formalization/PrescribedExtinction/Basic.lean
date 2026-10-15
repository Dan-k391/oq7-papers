import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Concrete three-dimensional coordinates and constitutive tensors.
No scattering existence, optical theorem, or response law is postulated here. -/
noncomputable section
namespace OQ7Prescribed

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Vector := EuclideanSpace ℂ (Fin 3)
abbrev Tensor := Matrix (Fin 3) (Fin 3) ℂ
abbrev Field := Position → Vector

def complexify (x : Position) : Vector := WithLp.toLp 2 (fun i => (x i : ℂ))

def basisR (j : Fin 3) : Position := WithLp.toLp 2 (Pi.single j 1)
def basisC (j : Fin 3) : Vector := WithLp.toLp 2 (Pi.single j 1)

def tensorApply (T : Tensor) (v : Vector) : Vector :=
  WithLp.toLp 2 (T.mulVec (WithLp.ofLp v))

def pairing (u v : Vector) : ℂ := ∑ i, star (u i) * v i
def bilinear (u v : Vector) : ℂ := ∑ i, u i * v i
def squareNorm (v : Vector) : ℝ := ∑ i, Complex.normSq (v i)
def quadratic (T : Tensor) (v : Vector) : ℂ := pairing v (tensorApply T v)

/-- Quadratic-form version of precisely (3): transpose reciprocity, real bounds,
strictly positive tensor loss, and an upper loss bound. -/
def MaterialAdmissible (P Q : ℝ) (ε : Tensor) : Prop :=
  ε.transpose = ε ∧
  (∀ v : Vector, squareNorm v ≤ (quadratic ε v).re ∧
    (quadratic ε v).re ≤ P * squareNorm v) ∧
  (∀ v : Vector, v ≠ 0 → 0 < (quadratic ε v).im) ∧
  (∀ v : Vector, (quadratic ε v).im ≤ Q * squareNorm v)

def rankOne (u : Position) : Tensor := fun i j => (u i : ℂ) * (u j : ℂ)
def rotatedAxis (θ : ℝ) : Position := WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0]
def layerPermittivity (a b ν : ℝ) (u : Position) : Tensor :=
  (1 + Complex.I * (ν : ℂ)) • (1 : Tensor) +
    ((a : ℂ) + Complex.I * (b : ℂ)) • rankOne u

def squareAperture (R : ℝ) : Set Position :=
  {x | -R / 2 < x 0 ∧ x 0 < R / 2 ∧ -R / 2 < x 1 ∧ x 1 < R / 2}
def bodyDomain (R h d : ℝ) : Set Position :=
  {x | x ∈ squareAperture R ∧ 0 < x 2 ∧ x 2 < h + d}

/-- A pair of actual constant three-by-three tensors in a bounded square slab. -/
structure TwoLayerBody where
  aperture : ℝ
  absorberThickness : ℝ
  plateThickness : ℝ
  absorberPermittivity : Tensor
  platePermittivity : Tensor
  aperture_pos : 0 < aperture
  absorberThickness_pos : 0 < absorberThickness
  plateThickness_pos : 0 < plateThickness

def TwoLayerBody.domain (B : TwoLayerBody) : Set Position :=
  bodyDomain B.aperture B.absorberThickness B.plateThickness

def TwoLayerBody.permittivity (B : TwoLayerBody) (x : Position) : Tensor := by
  classical
  exact if x ∈ B.domain then
    if x 2 < B.absorberThickness then B.absorberPermittivity else B.platePermittivity
  else 1

def TwoLayerBody.susceptibility (B : TwoLayerBody) (x : Position) : Tensor :=
  B.permittivity x - 1

def TwoLayerBody.admissible (B : TwoLayerBody) (P Q : ℝ) : Prop :=
  MaterialAdmissible P Q B.absorberPermittivity ∧
  MaterialAdmissible P Q B.platePermittivity

theorem squareNorm_nonneg (v : Vector) : 0 ≤ squareNorm v := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem squareNorm_eq_norm_sq (v : Vector) : squareNorm v = ‖v‖ ^ 2 := by
  simp only [squareNorm, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

theorem squareNorm_pos {v : Vector} (hv : v ≠ 0) : 0 < squareNorm v := by
  rw [squareNorm_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

theorem pairing_self (v : Vector) : pairing v v = (squareNorm v : ℂ) := by
  simp [pairing, squareNorm, Complex.normSq_eq_conj_mul_self]

theorem tensorApply_one (v : Vector) : tensorApply 1 v = v := by
  simp [tensorApply]

theorem rankOne_transpose (u : Position) : (rankOne u).transpose = rankOne u := by
  ext i j
  simp [rankOne, mul_comm]

theorem layerPermittivity_reciprocal (a b ν : ℝ) (u : Position) :
    (layerPermittivity a b ν u).transpose = layerPermittivity a b ν u := by
  simp [layerPermittivity, Matrix.transpose_add, rankOne_transpose]

theorem rotatedAxis_unit (θ : ℝ) : ‖rotatedAxis θ‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [rotatedAxis, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]

theorem susceptibility_zero_outside (B : TwoLayerBody) (x : Position)
    (hx : x ∉ B.domain) : B.susceptibility x = 0 := by
  simp [TwoLayerBody.susceptibility, TwoLayerBody.permittivity, hx]

end OQ7Prescribed
