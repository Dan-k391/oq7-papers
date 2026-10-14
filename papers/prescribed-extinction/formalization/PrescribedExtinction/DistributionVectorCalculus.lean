import PrescribedExtinction.NewtonCutoffIBP
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Cartesian derivatives and curl of the original scalar distributions.
All commutations are proved from the smoothness of actual test functions. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped Distributions

theorem testPartial_eq_fderiv (φ : ScalarTest) (i : Fin 3) (x : Position) :
    (testPartial i φ) x = fderiv ℝ (φ : Position → ℝ) x (basisR i) := by
  exact (testPartial_hasLineDerivAt φ i x).lineDeriv.symm.trans
    ((φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv)

theorem testPartial_second_eq_fderiv (φ : ScalarTest) (i j : Fin 3) (x : Position) :
    (testPartial j (testPartial i φ)) x =
      fderiv ℝ (fderiv ℝ (φ : Position → ℝ)) x (basisR j) (basisR i) := by
  have hderiv : DifferentiableAt ℝ (fderiv ℝ (φ : Position → ℝ)) x :=
    (φ.contDiff.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have he : (testPartial i φ : Position → ℝ) =
      fun y : Position => fderiv ℝ (φ : Position → ℝ) y (basisR i) :=
    funext (testPartial_eq_fderiv φ i)
  rw [testPartial_eq_fderiv, he]
  rw [fderiv_clm_apply hderiv (differentiableAt_const (basisR i))]
  simp

theorem testPartial_commute (φ : ScalarTest) (i j : Fin 3) :
    testPartial i (testPartial j φ) = testPartial j (testPartial i φ) := by
  ext x
  rw [testPartial_second_eq_fderiv, testPartial_second_eq_fderiv]
  exact (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).eq (basisR i) (basisR j)

theorem distributionPartial_commute (T : ScalarDistribution) (i j : Fin 3) :
    distributionPartial i (distributionPartial j T) =
      distributionPartial j (distributionPartial i T) := by
  ext φ
  simp only [distributionPartial, Distribution.lineDerivCLM_apply, neg_neg]
  change T (testPartial j (testPartial i φ)) = T (testPartial i (testPartial j φ))
  rw [testPartial_commute]

abbrev CartesianDistribution := Fin 3 → ScalarDistribution

def distributionLaplacian (T : ScalarDistribution) : ScalarDistribution :=
  ∑ i : Fin 3, distributionPartial i (distributionPartial i T)

def distributionDivergence (U : CartesianDistribution) : ScalarDistribution :=
  ∑ i : Fin 3, distributionPartial i (U i)

def distributionCurl (U : CartesianDistribution) : CartesianDistribution :=
  ![distributionPartial 1 (U 2) - distributionPartial 2 (U 1),
    distributionPartial 2 (U 0) - distributionPartial 0 (U 2),
    distributionPartial 0 (U 1) - distributionPartial 1 (U 0)]

theorem distributionCurl_gradient (T : ScalarDistribution) :
    distributionCurl (fun i => distributionPartial i T) = 0 := by
  funext i
  fin_cases i <;> simp [distributionCurl, distributionPartial_commute]

set_option maxHeartbeats 1000000 in
theorem distributionCurlCurl (U : CartesianDistribution) (i : Fin 3) :
    distributionCurl (distributionCurl U) i =
      distributionPartial i (distributionDivergence U) - distributionLaplacian (U i) := by
  fin_cases i <;>
    simp [distributionCurl, distributionDivergence, distributionLaplacian,
      Fin.sum_univ_three, map_sub, map_add]
  all_goals
    simp only [distributionPartial_commute]
    abel_nf
  rw [distributionPartial_commute (U 0) 0 1]

end OQ7Prescribed
