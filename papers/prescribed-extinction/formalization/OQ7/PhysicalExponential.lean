import OQ7.Fields
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.NoncommRing

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7
open scoped Matrix Matrix.Norms.Operator

def maxwellGenerator (k : ℝ) (n : ℂ) : Mat2 :=
  !![0, Complex.I * (k : ℂ); Complex.I * (k : ℂ) * n ^ 2, 0]

theorem homogeneousTransfer_hasDerivAt (k : ℝ) {n : ℂ} (hn : n ≠ 0) (z : ℝ) :
    HasDerivAt (homogeneousTransfer k n)
      (maxwellGenerator k n * homogeneousTransfer k n z) z := by
  have hd (i j : Fin 2) : HasDerivAt (fun u => homogeneousTransfer k n u i j)
      ((maxwellGenerator k n * homogeneousTransfer k n z) i j) z := by
    fin_cases i <;> fin_cases j
    · have he := electricField_hasDerivAt k hn 1 0 z
      change HasDerivAt (fun u => electricField k n 1 0 u) _ z at he
      simpa [homogeneousTransfer, maxwellGenerator, electricField, magneticField,
        Matrix.mul_apply, Fin.sum_univ_two] using he
    · have he := electricField_hasDerivAt k hn 0 1 z
      change HasDerivAt (fun u => electricField k n 0 1 u) _ z at he
      simpa [homogeneousTransfer, maxwellGenerator, electricField, magneticField,
        Matrix.mul_apply, Fin.sum_univ_two] using he
    · have he := magneticField_hasDerivAt k hn 1 0 z
      change HasDerivAt (fun u => magneticField k n 1 0 u) _ z at he
      simpa [homogeneousTransfer, maxwellGenerator, electricField, magneticField,
        Matrix.mul_apply, Fin.sum_univ_two] using he
    · have he := magneticField_hasDerivAt k hn 0 1 z
      change HasDerivAt (fun u => magneticField k n 0 1 u) _ z at he
      simpa [homogeneousTransfer, maxwellGenerator, electricField, magneticField,
        Matrix.mul_apply, Fin.sum_univ_two] using he
  exact (hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hd i j)

/-- The layer exponential is derived from the existing exact Maxwell transfer. -/
theorem homogeneousTransfer_eq_exp (k : ℝ) {n : ℂ} (hn : n ≠ 0) (z : ℝ) :
    homogeneousTransfer k n z = NormedSpace.exp (z • maxwellGenerator k n) := by
  let G := maxwellGenerator k n
  let V : ℝ → Mat2 := fun u => NormedSpace.exp ((-u) • G) * homogeneousTransfer k n u
  have hV (u : ℝ) : HasDerivAt V 0 u := by
    have he0 : HasDerivAt (fun v : ℝ => NormedSpace.exp (v • G))
        (NormedSpace.exp ((-u) • G) * G) (-u) := hasDerivAt_exp_smul_const G (-u)
    have he := he0.scomp u ((hasDerivAt_id u).neg)
    have hp := he.mul (homogeneousTransfer_hasDerivAt k hn u)
    convert hp using 1 <;> first
      | rfl
      | simp [G, mul_assoc]
  have hc : V z = V 0 := is_const_of_deriv_eq_zero
    (fun u => (hV u).differentiableAt) (fun u => (hV u).deriv) z 0
  have hzero : V 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [V, homogeneousTransfer]
  rw [hzero] at hc
  have hinv : NormedSpace.exp (z • G) * NormedSpace.exp ((-z) • G) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.smul_left (Commute.smul_right (Commute.refl G) _) _)]
    simp
  have hm := congrArg (fun X : Mat2 => NormedSpace.exp (z • G) * X) hc
  simpa only [V, ← mul_assoc, hinv, one_mul, mul_one] using hm

theorem layerTransfer_eq_exp (k : ℝ) {layer : HomogeneousLayer} (hp : 1 ≤ layer.p) :
    layerTransfer k layer =
      NormedSpace.exp (layer.width • maxwellGenerator k (refractiveIndex layer)) :=
  homogeneousTransfer_eq_exp k (refractiveIndex_ne_zero hp) layer.width

#print axioms homogeneousTransfer_hasDerivAt
#print axioms homogeneousTransfer_eq_exp
#print axioms layerTransfer_eq_exp
end OQ7
