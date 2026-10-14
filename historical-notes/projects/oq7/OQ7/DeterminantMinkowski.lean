import OQ7.TwoPort
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
namespace OQ7
open scoped ComplexOrder

theorem determinant_lorentz_mixed {a d b e zr zi wr wi da db : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hda : 0 ≤ da) (hdb : 0 ≤ db)
    (hea : da = a * d - zr ^ 2 - zi ^ 2)
    (heb : db = b * e - wr ^ 2 - wi ^ 2) :
    2 * (Real.sqrt da * Real.sqrt db + zr * wr + zi * wi) ≤ a * e + b * d := by
  have hsda := Real.sq_sqrt hda
  have hsdb := Real.sq_sqrt hdb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (![Real.sqrt da, zr, zi] : Fin 3 → ℝ) (![Real.sqrt db, wr, wi] : Fin 3 → ℝ)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hcs
  change (Real.sqrt da * Real.sqrt db + zr * wr + zi * wi) ^ 2 ≤
    (Real.sqrt da ^ 2 + zr ^ 2 + zi ^ 2) *
      (Real.sqrt db ^ 2 + wr ^ 2 + wi ^ 2) at hcs
  have hac : Real.sqrt da ^ 2 + zr ^ 2 + zi ^ 2 = a * d := by linarith
  have hbc : Real.sqrt db ^ 2 + wr ^ 2 + wi ^ 2 = b * e := by linarith
  rw [hac, hbc] at hcs
  have hupper : (a * d) * (b * e) ≤ ((a * e + b * d) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a * e - b * d)]
  have hcross := hcs.trans hupper
  have hn : 0 ≤ (a * e + b * d) / 2 :=
    div_nonneg (add_nonneg (mul_nonneg ha he) (mul_nonneg hb hd)) (by norm_num)
  by_cases hdot : 0 ≤ Real.sqrt da * Real.sqrt db + zr * wr + zi * wi
  · have h := (sq_le_sq₀ hdot hn).mp hcross
    linarith
  · linarith

theorem posSemidef_det_coordinates {A : Mat2} (hA : A.PosSemidef) :
    A.det.re = (A 0 0).re * (A 1 1).re - (A 0 1).re ^ 2 - (A 0 1).im ^ 2 := by
  have hi0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 0))).2
  have hi1 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 1))).2
  have hoff := hA.isHermitian.apply 1 0
  rw [Matrix.det_fin_two, ← hoff]
  simp only [Complex.mul_re, Complex.sub_re, hi0.symm, hi1.symm,
    Complex.star_def, Complex.conj_re, Complex.conj_im, zero_mul]
  ring

theorem posSemidef_det_add_cross {A B : Mat2} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A + B).det.re = A.det.re + B.det.re +
      (A 0 0).re * (B 1 1).re + (B 0 0).re * (A 1 1).re -
      2 * ((A 0 1).re * (B 0 1).re + (A 0 1).im * (B 0 1).im) := by
  rw [posSemidef_det_coordinates (hA.add hB), posSemidef_det_coordinates hA,
    posSemidef_det_coordinates hB]
  simp only [Matrix.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem posSemidef_sqrt_det_minkowski {A B : Mat2}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Real.sqrt A.det.re + Real.sqrt B.det.re ≤ Real.sqrt (A + B).det.re := by
  have ha := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 0))).1
  have hd := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 1))).1
  have hb := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := 0))).1
  have he := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := 1))).1
  have hda := (Complex.nonneg_iff.mp hA.det_nonneg).1
  have hdb := (Complex.nonneg_iff.mp hB.det_nonneg).1
  have hcross := determinant_lorentz_mixed ha hd hb he hda hdb
    (posSemidef_det_coordinates hA) (posSemidef_det_coordinates hB)
  have hsda := Real.sq_sqrt hda
  have hsdb := Real.sq_sqrt hdb
  have hdet := posSemidef_det_add_cross hA hB
  have hbound : (Real.sqrt A.det.re + Real.sqrt B.det.re) ^ 2 ≤ (A + B).det.re := by
    nlinarith
  exact Real.le_sqrt_of_sq_le hbound

theorem posSemidef_sqrt_det_mono {A B : Mat2}
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) :
    Real.sqrt A.det.re ≤ Real.sqrt B.det.re := by
  have h := posSemidef_sqrt_det_minkowski hA hBA
  rw [add_sub_cancel] at h
  exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans h

theorem posSemidef_sqrt_det_sum {ι : Type*} (s : Finset ι) (A : ι → Mat2)
    (hA : ∀ i ∈ s, (A i).PosSemidef) :
    (∑ i ∈ s, Real.sqrt (A i).det.re) ≤ Real.sqrt (∑ i ∈ s, A i).det.re := by
  classical
  revert hA
  induction s using Finset.induction_on with
  | empty => intro hA; simp
  | @insert i s hi ih =>
      intro hA
      have hiA := hA i (Finset.mem_insert_self i s)
      have hsA : ∀ j ∈ s, (A j).PosSemidef :=
        fun j hj => hA j (Finset.mem_insert_of_mem hj)
      have hsum : (∑ j ∈ s, A j).PosSemidef := Matrix.posSemidef_sum s hsA
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfirst : Real.sqrt (A i).det.re + (∑ j ∈ s, Real.sqrt (A j).det.re) ≤
          Real.sqrt (A i).det.re + Real.sqrt (∑ j ∈ s, A j).det.re :=
        add_le_add le_rfl (ih hsA)
      have hsecond := posSemidef_sqrt_det_minkowski hiA hsum
      simpa only [add_comm] using hfirst.trans hsecond

theorem posSemidef_sqrt_det_aggregate {ι : Type*} (s : Finset ι) (A : ι → Mat2)
    (total : Mat2) (hA : ∀ i ∈ s, (A i).PosSemidef)
    (hrest : (total - ∑ i ∈ s, A i).PosSemidef) :
    (∑ i ∈ s, Real.sqrt (A i).det.re) ≤ Real.sqrt total.det.re := by
  have hsum : (∑ i ∈ s, A i).PosSemidef := Matrix.posSemidef_sum s hA
  exact (posSemidef_sqrt_det_sum s A hA).trans (posSemidef_sqrt_det_mono hsum hrest)

#print axioms determinant_lorentz_mixed
#print axioms posSemidef_det_coordinates
#print axioms posSemidef_det_add_cross
#print axioms posSemidef_sqrt_det_minkowski
#print axioms posSemidef_sqrt_det_mono
#print axioms posSemidef_sqrt_det_sum
#print axioms posSemidef_sqrt_det_aggregate
end OQ7
