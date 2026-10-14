import OQ7.Layers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OQ7

open scoped Matrix

noncomputable def electricField (k : ℝ) (n E₀ H₀ : ℂ) (z : ℝ) : ℂ :=
  E₀ * Complex.cos ((k : ℂ) * n * (z : ℂ)) +
    Complex.I * H₀ * Complex.sin ((k : ℂ) * n * (z : ℂ)) / n

noncomputable def magneticField (k : ℝ) (n E₀ H₀ : ℂ) (z : ℝ) : ℂ :=
  Complex.I * n * E₀ * Complex.sin ((k : ℂ) * n * (z : ℂ)) +
    H₀ * Complex.cos ((k : ℂ) * n * (z : ℂ))

theorem electricField_hasDerivAt (k : ℝ) {n : ℂ} (hn : n ≠ 0)
    (E₀ H₀ : ℂ) (z : ℝ) :
    HasDerivAt (electricField k n E₀ H₀)
      (Complex.I * (k : ℂ) * magneticField k n E₀ H₀ z) z := by
  have harg := (hasDerivAt_id (z : ℂ)).const_mul ((k : ℂ) * n)
  have hc := (Complex.hasDerivAt_cos ((k : ℂ) * n * (z : ℂ))).comp (z : ℂ) harg
  have hs := (Complex.hasDerivAt_sin ((k : ℂ) * n * (z : ℂ))).comp (z : ℂ) harg
  have hd := ((hc.const_mul E₀).add ((hs.const_mul (Complex.I * H₀)).div_const n)).comp_ofReal
  convert hd using 1
  · rfl
  · dsimp [magneticField]
    field_simp
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]

theorem magneticField_hasDerivAt (k : ℝ) {n : ℂ} (hn : n ≠ 0)
    (E₀ H₀ : ℂ) (z : ℝ) :
    HasDerivAt (magneticField k n E₀ H₀)
      (Complex.I * (k : ℂ) * n ^ 2 * electricField k n E₀ H₀ z) z := by
  have harg := (hasDerivAt_id (z : ℂ)).const_mul ((k : ℂ) * n)
  have hc := (Complex.hasDerivAt_cos ((k : ℂ) * n * (z : ℂ))).comp (z : ℂ) harg
  have hs := (Complex.hasDerivAt_sin ((k : ℂ) * n * (z : ℂ))).comp (z : ℂ) harg
  have hd := ((hs.const_mul (Complex.I * n * E₀)).add (hc.const_mul H₀)).comp_ofReal
  convert hd using 1
  · rfl
  · dsimp [electricField]
    field_simp
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]

theorem electricField_second_deriv (k : ℝ) {n : ℂ} (hn : n ≠ 0)
    (E₀ H₀ : ℂ) (z : ℝ) :
    deriv (deriv (electricField k n E₀ H₀)) z =
      -(k : ℂ) ^ 2 * n ^ 2 * electricField k n E₀ H₀ z := by
  have hfirst : deriv (electricField k n E₀ H₀) =
      fun x => Complex.I * (k : ℂ) * magneticField k n E₀ H₀ x := by
    funext x
    exact (electricField_hasDerivAt k hn E₀ H₀ x).deriv
  rw [hfirst]
  have hsecond := (magneticField_hasDerivAt k hn E₀ H₀ z).const_mul
    (Complex.I * (k : ℂ))
  rw [hsecond.deriv]
  ring_nf
  simp [Complex.I_sq]

theorem electricField_state_coordinate {k : ℝ} (hk : k ≠ 0) {n : ℂ} (hn : n ≠ 0)
    (E₀ H₀ : ℂ) (z : ℝ) :
    deriv (electricField k n E₀ H₀) z / (Complex.I * (k : ℂ)) =
      magneticField k n E₀ H₀ z := by
  rw [(electricField_hasDerivAt k hn E₀ H₀ z).deriv]
  have hkn : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  field_simp

theorem homogeneousField_initial (k : ℝ) (n E₀ H₀ : ℂ) :
    electricField k n E₀ H₀ 0 = E₀ ∧ magneticField k n E₀ H₀ 0 = H₀ := by
  simp [electricField, magneticField]

theorem homogeneousField_transfer (k : ℝ) (n E₀ H₀ : ℂ) (z : ℝ) :
    homogeneousTransfer k n z *ᵥ ![E₀, H₀] =
      ![electricField k n E₀ H₀ z, magneticField k n E₀ H₀ z] := by
  ext i
  fin_cases i <;> simp [homogeneousTransfer, electricField, magneticField,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

noncomputable def layerElectricField (k : ℝ) (layer : HomogeneousLayer)
    (E₀ H₀ : ℂ) : ℝ → ℂ := electricField k (refractiveIndex layer) E₀ H₀

noncomputable def layerMagneticField (k : ℝ) (layer : HomogeneousLayer)
    (E₀ H₀ : ℂ) : ℝ → ℂ := magneticField k (refractiveIndex layer) E₀ H₀

theorem layerElectricField_maxwell (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (E₀ H₀ : ℂ) (z : ℝ) :
    HasDerivAt (layerElectricField k layer E₀ H₀)
      (Complex.I * (k : ℂ) * layerMagneticField k layer E₀ H₀ z) z := by
  exact electricField_hasDerivAt k (refractiveIndex_ne_zero hp) E₀ H₀ z

theorem layerMagneticField_maxwell (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (E₀ H₀ : ℂ) (z : ℝ) :
    HasDerivAt (layerMagneticField k layer E₀ H₀)
      (Complex.I * (k : ℂ) * relativePermittivity layer *
        layerElectricField k layer E₀ H₀ z) z := by
  simpa only [layerMagneticField, layerElectricField, refractiveIndex_sq] using
    magneticField_hasDerivAt k (refractiveIndex_ne_zero hp) E₀ H₀ z

theorem layerElectricField_helmholtz (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (E₀ H₀ : ℂ) (z : ℝ) :
    deriv (deriv (layerElectricField k layer E₀ H₀)) z +
      (k : ℂ) ^ 2 * relativePermittivity layer * layerElectricField k layer E₀ H₀ z = 0 := by
  change deriv (deriv (electricField k (refractiveIndex layer) E₀ H₀)) z + _ = 0
  rw [electricField_second_deriv k (refractiveIndex_ne_zero hp), refractiveIndex_sq]
  unfold layerElectricField
  ring

theorem layerField_transfer_boundary (k : ℝ) (layer : HomogeneousLayer) (E₀ H₀ : ℂ) :
    layerTransfer k layer *ᵥ ![E₀, H₀] =
      ![layerElectricField k layer E₀ H₀ layer.width,
        layerMagneticField k layer E₀ H₀ layer.width] := by
  exact homogeneousField_transfer k (refractiveIndex layer) E₀ H₀ layer.width

/-- The paper's normalized directed flux, in the actual field-state coordinates. -/
def directedFlux (E H : ℂ) : ℝ := (star E * H).re

theorem directedFlux_derivative_algebra (k p q : ℝ) (E H : ℂ) :
    (star (Complex.I * (k : ℂ) * H) * H +
      star E * (Complex.I * (k : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ)) * E)).re =
      -k * q * Complex.normSq E := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem layerDirectedFlux_hasDerivAt (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (E₀ H₀ : ℂ) (z : ℝ) :
    HasDerivAt (fun x => directedFlux (layerElectricField k layer E₀ H₀ x)
      (layerMagneticField k layer E₀ H₀ x))
      (-k * layer.q * Complex.normSq (layerElectricField k layer E₀ H₀ z)) z := by
  have hE := layerElectricField_maxwell k hp E₀ H₀ z
  have hH := layerMagneticField_maxwell k hp E₀ H₀ z
  have hprod := hE.star.mul hH
  have hflux := Complex.reCLM.hasFDerivAt.comp_hasDerivAt z hprod
  convert hflux using 1
  · rfl
  · exact (directedFlux_derivative_algebra k layer.p layer.q
      (layerElectricField k layer E₀ H₀ z) (layerMagneticField k layer E₀ H₀ z)).symm

#print axioms electricField_hasDerivAt
#print axioms magneticField_hasDerivAt
#print axioms electricField_second_deriv
#print axioms electricField_state_coordinate
#print axioms homogeneousField_initial
#print axioms homogeneousField_transfer
#print axioms layerElectricField_maxwell
#print axioms layerMagneticField_maxwell
#print axioms layerElectricField_helmholtz
#print axioms layerField_transfer_boundary
#print axioms directedFlux_derivative_algebra
#print axioms layerDirectedFlux_hasDerivAt

end OQ7
