import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

section
variable {H S : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]

def woodburyElectricOperator (K : H →L[ℂ] H) (J : S →L[ℂ] H) (P : H →L[ℂ] S)
    (C : S →L[ℂ] S) : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - K ∘L J ∘L C ∘L P

def woodburyElectricInverse (K : H →L[ℂ] H) (J : S →L[ℂ] H) (P : H →L[ℂ] S)
    (e : S ≃L[ℂ] S) : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - K ∘L J ∘L e.symm.toContinuousLinearMap ∘L P

theorem woodburyElectricOperator_right_inverse (K : H →L[ℂ] H) (J : S →L[ℂ] H) (P : H →L[ℂ] S)
    (C D : S →L[ℂ] S) (hCD : C ∘L D = ContinuousLinearMap.id ℂ S)
    (e : S ≃L[ℂ] S) (he : e.toContinuousLinearMap = P ∘L K ∘L J - D) (x : H) :
    woodburyElectricOperator K J P C (woodburyElectricInverse K J P e x) = x := by
  let a := e.symm (P x)
  have hD : C (D a) = a := congrArg (fun T : S →L[ℂ] S => T a) hCD
  have ha : P (K (J a)) - D a = P x := by
    have h := e.apply_symm_apply (P x)
    change e.toContinuousLinearMap a = P x at h
    rw [he] at h
    exact h
  have hCa : C (P x - P (K (J a))) = -a := by
    rw [← ha, sub_sub_cancel_left, map_neg, hD]
  change (x - K (J a)) - K (J (C (P (x - K (J a))))) = x
  rw [map_sub, hCa, map_neg, map_neg]
  abel

theorem woodburyElectricOperator_left_inverse (K : H →L[ℂ] H) (J : S →L[ℂ] H) (P : H →L[ℂ] S)
    (C D : S →L[ℂ] S) (hDC : D ∘L C = ContinuousLinearMap.id ℂ S)
    (e : S ≃L[ℂ] S) (he : e.toContinuousLinearMap = P ∘L K ∘L J - D) (x : H) :
    woodburyElectricInverse K J P e (woodburyElectricOperator K J P C x) = x := by
  have hD : D (C (P x)) = P x := congrArg (fun T : S →L[ℂ] S => T (P x)) hDC
  have ha : e.symm (P (x - K (J (C (P x))))) = -C (P x) := by
    apply e.injective
    rw [e.apply_symm_apply, map_neg]
    change P (x - K (J (C (P x)))) = -(e.toContinuousLinearMap (C (P x)))
    rw [he]
    change P (x - K (J (C (P x)))) = -(P (K (J (C (P x)))) - D (C (P x)))
    rw [map_sub, hD]
    abel
  change (x - K (J (C (P x)))) - K (J (e.symm (P (x - K (J (C (P x))))))) = x
  rw [ha, map_neg, map_neg]
  abel

def woodburyElectricUnit (K : H →L[ℂ] H) (J : S →L[ℂ] H) (P : H →L[ℂ] S)
    (C D : S →L[ℂ] S) (hCD : C ∘L D = ContinuousLinearMap.id ℂ S)
    (hDC : D ∘L C = ContinuousLinearMap.id ℂ S)
    (e : S ≃L[ℂ] S) (he : e.toContinuousLinearMap = P ∘L K ∘L J - D) : (H →L[ℂ] H)ˣ where
  val := woodburyElectricOperator K J P C
  inv := woodburyElectricInverse K J P e
  val_inv := by
    ext x
    exact woodburyElectricOperator_right_inverse K J P C D hCD e he x
  inv_val := by
    ext x
    exact woodburyElectricOperator_left_inverse K J P C D hDC e he x

theorem woodburySusceptibility_inverse_apply (K : H →L[ℂ] H) (J : S →L[ℂ] H) (P : H →L[ℂ] S)
    (C D : S →L[ℂ] S) (hCD : C ∘L D = ContinuousLinearMap.id ℂ S)
    (e : S ≃L[ℂ] S) (he : e.toContinuousLinearMap = P ∘L K ∘L J - D) (x : H) :
    J (C (P (woodburyElectricInverse K J P e x))) = -J (e.symm (P x)) := by
  let a := e.symm (P x)
  have hD : C (D a) = a := congrArg (fun T : S →L[ℂ] S => T a) hCD
  have ha : P (K (J a)) - D a = P x := by
    have h := e.apply_symm_apply (P x)
    change e.toContinuousLinearMap a = P x at h
    rw [he] at h
    exact h
  have hCa : C (P x - P (K (J a))) = -a := by
    rw [← ha, sub_sub_cancel_left, map_neg, hD]
  change J (C (P (x - K (J a)))) = -J a
  rw [map_sub, hCa, map_neg]

end
end OQ7Prescribed
