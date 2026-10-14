import PrescribedExtinction.DyadicMaxwellSource

noncomputable section
namespace OQ7Prescribed

theorem distributionDivergence_curl (U : CartesianDistribution) :
    distributionDivergence (distributionCurl U) = 0 := by
  simp only [distributionDivergence, distributionCurl, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_sub]
  rw [distributionPartial_commute (U 2) 0 1, distributionPartial_commute (U 0) 1 2,
    distributionPartial_commute (U 1) 2 0]
  abel

theorem distributionDivergence_complex_smul (a : ℂ) (U : CartesianDistribution) :
    distributionDivergence (a • U) = a • distributionDivergence U := by
  simp [distributionDivergence, distributionPartial_complex_smul, Finset.smul_sum]

/-- Genuine homogeneous distributional Maxwell equations imply the scalar
Helmholtz equations and zero divergence, without an elliptic regularity assumption. -/
theorem vacuumDistribution_Maxwell_Helmholtz (k : ℝ) (hk : 0 < k) (E H : CartesianDistribution)
    (he : distributionCurl E = (Complex.I * (k : ℂ)) • H)
    (hh : distributionCurl H = (-Complex.I * (k : ℂ)) • E) :
    distributionDivergence E = 0 ∧ distributionDivergence H = 0 ∧
      (∀ i, distributionLaplacian (E i) + ((k ^ 2 : ℝ) : ℂ) • E i = 0) ∧
      (∀ i, distributionLaplacian (H i) + ((k ^ 2 : ℝ) : ℂ) • H i = 0) := by
  have hak : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne')
  have hbk : -Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hk.ne')
  have hdE : distributionDivergence E = 0 := by
    have h := congrArg distributionDivergence hh
    rw [distributionDivergence_curl, distributionDivergence_complex_smul] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hbk
  have hdH : distributionDivergence H = 0 := by
    have h := congrArg distributionDivergence he
    rw [distributionDivergence_curl, distributionDivergence_complex_smul] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hak
  have ha : (Complex.I * (k : ℂ)) * (-Complex.I * (k : ℂ)) = ((k ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
    ring_nf
    simp [Complex.I_sq]
  have hce : distributionCurl (distributionCurl E) = ((k ^ 2 : ℝ) : ℂ) • E := by
    rw [he, distributionCurl_complex_smul, hh, smul_smul, ha]
  have hch : distributionCurl (distributionCurl H) = ((k ^ 2 : ℝ) : ℂ) • H := by
    rw [hh, distributionCurl_complex_smul, he, smul_smul, mul_comm, ha]
  refine ⟨hdE, hdH, ?_, ?_⟩
  · intro i
    have h := congrFun hce i
    rw [distributionCurlCurl, hdE] at h
    simp only [map_zero, zero_sub, Pi.smul_apply] at h
    exact neg_eq_iff_add_eq_zero.mp h
  · intro i
    have h := congrFun hch i
    rw [distributionCurlCurl, hdH] at h
    simp only [map_zero, zero_sub, Pi.smul_apply] at h
    exact neg_eq_iff_add_eq_zero.mp h

end OQ7Prescribed
